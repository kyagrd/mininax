-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE CPP, TemplateHaskell,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             OverlappingInstances,
             IncoherentInstances,
             OverloadedStrings,
             GADTs,
             NoMonomorphismRestriction,
             ScopedTypeVariables
  #-}

module Infer where

#include "macros.h"

import Syntax

import Data.Char
import Data.List
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.State.Lazy
import Language.LBNF.Runtime
import Parser (ty2Type)
import Generics.RepLib.Unify hiding (solveUnification)
import Unbound.LocallyNameless hiding (subst, Con, union)
import qualified Unbound.LocallyNameless as LN
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import GHC.Exts( IsString(..) )
import Debug.Trace
-- trace _ a = a

catchErrorThrowWithMsg m f = m `catchError` (\e -> throwError . strMsg $ f e)


instance HasVar (Name PSUT) PSUT where
  is_var (Var nm) = Just nm
  is_var _ = Nothing
  var = Var

instance (Eq n, Show n, Show a, HasVar n a) => Unify n a String where
   unifyStep _ = unifyStepEq

instance (Eq n, Show n, Show a, HasVar n a) => Unify n a (Name s) where
   unifyStep _ = unifyStepEq

instance (Alpha n, Eq n, Show n, HasVar n PSUT) => Unify n PSUT (Bind n PSUT) where
   unifyStep _ b1 b2 
       | b1 `aeq` b2 = return ()
       | otherwise   =
           do (e1,e2) <- runFreshMT $
                         do { (_,e1) <- unbind b1
                            ; (_,e2) <- unbind b2
                            ; return (e1,e2) }
              -- trace ("trace in instance Unify n a (Bind n a): " ++ show (e1,e2)) $
              unifyStep undefined e1 e2

instance (Eq n, Show n, HasVar n PSUT) => Unify n PSUT PSUT where
   unifyStep (dum :: Proxy(n,PSUT)) t1 t2 | isTm t1 && isTm t2 =
    do a1 <- runFreshMT (norm [] t1)
       a2 <- runFreshMT (norm [] t2)
       -- trace ("trace 1 in instance Unify n PSUT PSUT): " ++ show (a1,a2)) $
       case ((is_var a1) :: Maybe n, (is_var a2) :: Maybe n) of
            (Just n1, Just n2) ->  if n1 == n2
                                     then return ()
                                     else addSub n1 (var n2);
            (Just n1, _) -> addSub n1 a2
            (_, Just n2) ->  addSub n2 a1
            (_, _) -> unifyStepR1 rep1 dum a1 a2
       where
       addSub n t = extendSubstitution (n, t)
   unifyStep (dum :: Proxy(n,PSUT)) a1 a2 =
      -- trace ("trace 2 in instance Unify n PSUT PSUT): " ++ show (a1,a2)) $
       case ((is_var a1) :: Maybe n, (is_var a2) :: Maybe n) of
           (Just n1, Just n2) ->  if n1 == n2
                                    then return ()
                                    else addSub n1 (var n2);
           (Just n1, _) -> addSub n1 a2
           (_, Just n2) ->  addSub n2 a1
           (_, _) -> unifyStepR1 rep1 dum a1 a2
       where
       addSub n t = extendSubstitution (n, t)


-- modified the Generics.Replib.Unify version to throwError rather than error
-- TODO Can be even better if we pass curret stat rather than (Ustate cs [])?
--      somehow this idea doesn't work ... [] replaced with current subst loops
-- solveUnification :: (HasVar n a, Eq n, Show n, Show a, Rep1 (UnifySubD n a) a) => [(a, a)] -> Either UnifyError [(n, a)]

solveUnification (eqs :: [(a, a)]) =
     case r of Left e  -> throwError e
               Right _ -> return $ uSubst final
     where
     (r, final) = runState (runErrorT rwConstraints) (UState cs [])
     cs = [(UC dict a1 a2) | (a1, a2) <- eqs]
     rwConstraints :: UM n a ()
     rwConstraints =
       do c <- dequeueConstraint
          case c of Just (UC d a1 a2) ->
                            do unifyStepD d (undefined :: Proxy (n, a)) a1 a2
                               rwConstraints
                    Nothing -> return ()

envApply env = foldr (.) id (map (uncurry LN.subst) env)

substBackquote env = envApply [(string2Name('`':show x)::TmName,t) | (x,t)<-env]

mgu t1 t2 = do
  case solveUnification [(t1, t2)] of
    Left e  -> throwError (strMsg $ e ++ "\n\t"++ errstr)
    Right u -> return u
  where errstr = "cannot unify "++printTree t1++" and "++printTree t2

mguMany ps = do
  case solveUnification ps of
    Left e  -> throwError (strMsg $ e ++ "\n\t" ++ errstr)
    Right u -> return u
  where errstr = "cannot unify \n" ++
                 ( concat [ "\t"++printTree t1++" and "++printTree t2++"\n"
                          | (t1,t2)<-ps ] )

lift2 = lift . lift
getSubst = do { UState _ s <- lift get; return s }

extendSubst (x,Var y) | x < y = extendSubst (y,Var x)
                      | x== y = return ()
extendSubst (x,t) =
  do u <- getSubst
     case lookup x u of
       Nothing -> extendSubstitution (x,t)
       Just t' -> mapM_ extendSubst =<< mgu t t'

unify t1 t2 = -- trace ("unify ("++show t1++") ("++show t2++")") $
  do u <- getSubst
     mapM_ extendSubst =<< mgu (uapply u t1) (uapply u t2)

unifyMany ps = do u <- getSubst
                  mapM_ extendSubst =<< mguMany (map (uapply u) ps)


type KCtx = [(TyName,KiSch)]
type KI = FreshMT (StateT [(TyName,Ki)]
                          (ErrorT UnifyError
                                  (State (UnificationState KiName Ki))))

type KiSch = Bind ([TmName],[TyName],[KiName]) Ki

ki :: KCtx -> Ctx -> Env -> Ty -> KI Ki
ki kctx ictx env (Var x)
   | head(show x) == '`' = throwError(strMsg $ show x++
                                      " backquoted variable not allowed (ki)")
ki kctx ictx env (Var x) =
  case lookup x kctx of
    Just kisch -> return =<< freshKiInst kisch -- ki vars must be simple though
    Nothing -> do
      ps <- lift get
      case lookup x ps of
        Just k -> return k
        Nothing -> throwError(strMsg $ "ty var "++show x++" undefined tyvar")
ki kctx ictx env (TCon x) =
  case lookup x kctx of
    Just kisch -> return =<< freshKiInst kisch
    Nothing -> do
      ps <- lift get
      case lookup x ps of
        Just k -> return k
        Nothing -> throwError(strMsg $ "ty con "++show x++" undefined tycon")
ki kctx ictx env (TArr t1 t2) =
  do k1 <- ki kctx ictx env t1
     k2 <- ki kctx ictx env t2
     lift2 $ unify Star k1
     lift2 $ unify Star k2
     return Star
ki kctx ictx env (TApp t1 (Right t2)) =
  do k1 <- ki kctx ictx env t1
     k2 <- ki kctx ictx env t2
     k <- Var <$> fresh "k_TApp1_"
     lift2 $ unify (KArr (Right k2) k) k1
     return k
ki kctx ictx env (TApp t1 (Left e2)) =
  do k1 <- ki kctx ictx env t1
     t2 <- ti kctx ictx [] env e2
     k <- Var <$> fresh "k_TApp2_"
     lift2 $ unify (KArr (Left t2) k) k1
     return k
ki kctx ictx env (TFix t) =
  do k1 <- ki kctx ictx env t
     k <- Var <$> fresh "k_TFix_"
     lift2 $ unify (KArr (Right k) k) k1
     return k


freshTmName' x = freshTmName x =<< (Var <$> freshTyName "t" Star)

freshTmName x t = do nm <- fresh x
                     lift $ modify ((nm,t) :)
                     return nm


freshTyName' x = freshTyName x =<< (Var <$> fresh "k")

freshTyName x k = do
  nm <- fresh x
  lift $ modify ((nm,k) :)
  () <- trace ("\nfreshTyName: adding "++show (nm,k)++" to ps") $ return ()
  return nm

freshKiInst sch = do
  ((_,ts,xs), k) <- unbind sch
  psR <- sequence $ [(,) x <$> (Var <$> fresh "k_KiInstR_") | x<-ts]
  psL <- sequence $ [(,) x <$> (Var <$> freshTyName "t_KiInstL_" Star) | x<-xs]
  lift $ modify ((psL++psR)++)
  return k

freshTyInst sch = do
  (vs, ty) <- unbind sch
  psR <- sequence $ [(,) x <$> (Var <$> fresh "k_TyInstR_") | Right x<-vs]
  psL <- sequence $ [(,) x <$> (Var <$> freshTyName "t_TyInstL_" Star) | Left x<-vs]
  lift $ modify ((psL++psR)++)
  return ty


closeKi kctx ctx as k = do -- as are extra vars that should not to generalize
  -- () <- trace ("closeKi "++show k
  --                    ++"\n\t"++show freeKiVars
  --                    ++"\n\t"++show freeTyVars
  --                    ++"\n\t"++show freeTmVars) $ return ()
  -- () <- trace ("\n\t freeKiVars = "++show freeKiVars
  --            ++"\n\t freeTyVars = "++show freeTyVars
  --            ++"\n\t freeTmVars = "++show freeTmVars ) $ return ()
  -- () <- trace ("\n\t kctx = "++show kctx
  --            ++"\n\t ctx = "++show ctx ) $ return ()
  -- () <- trace ("\n\t fv k = "++show(fv k::[KiName])) $ return ()
  unless (null $ freeKiVars `intersect` freeTyVars)
    (throwError . strMsg $
       "duplicate kind/type vars "++show (freeKiVars `intersect` freeTyVars)++
       "when generalizing "++show k)
  unless (null $ freeTyVars `intersect` freeTmVars)
    (throwError . strMsg $
       "duplicate type/term vars "++show (freeTyVars `intersect` freeTmVars)++
       "when generalizing "++show k)
  unless (null $ freeKiVars `intersect` freeTmVars)
    (throwError . strMsg $
       "duplicate kind/term vars "++show (freeKiVars `intersect` freeTmVars)++
       "when generalizing "++show k)
  return $ bind (freeKiVars,freeTyVars,freeTmVars) k
  where
  freeKiVars = nub (fvKi k) \\ (fv ctx ++ fv kctx ++ as)
  freeTyVars = nub (concatMap fvTyInTy $ tysInKi k) \\ (fv ctx ++ fv kctx ++ as)
  freeTmVars = nub (concatMap fvTmInTy $ tysInKi k) \\ (fv ctx ++ fv kctx ++ as)


closeTy kctx ctx ty = do
  unless (null $ freeLvars `intersect` freeRvars)
    (throwError . strMsg $
       "duplicate type/term vars "++show (freeLvars `intersect` freeRvars)++
       "when generalizing "++show ty)
  return $ bind (map Right freeRvars ++ map Left freeLvars) ty
  where
  freeLvars = nub (fvTmInTy ty) \\ (fv ctx ++ fv kctx)
  freeRvars = nub (fvTyInTy ty) \\ (fv ctx ++ fv kctx)


-- assumes that it is applied only to kinds
fvKi (Var x)              = [x]
fvKi Star                 = []
fvKi (KArr (Right k1) k2) = fvKi k1 ++ fvKi k2
fvKi (KArr (Left  _ ) k2) = fvKi k2
fvKi t                    = error (show t ++ " is not kind")

tysInKi (Var _)              = []
tysInKi Star                 = []
tysInKi (KArr (Left  t ) k ) = t : tysInKi k
tysInKi (KArr (Right k1) k2) = tysInKi k1 ++ tysInKi k2
tysInKi t                    = error (show t ++ " is not kind")

-- sorry no generic programming in here :( TODO is there a way?
fvTmInTy t | not(isTy t) = []
fvTmInTy (Var _) = []
fvTmInTy (TCon _) = []
fvTmInTy (TArr t1 t2) = fvTmInTy t1 ++ fvTmInTy t2
fvTmInTy (TApp t1 (Right t2)) = fvTmInTy t1 ++ fvTmInTy t2
fvTmInTy (TApp t1 (Left  t2)) = fvTmInTy t1 ++ fv t2
fvTmInTy (TFix t) = fvTmInTy t
fvTmInTy _ = error "this should be unrechable for fvTmInTy" 

fvTyInTy t | not(isTy t) = []
fvTyInTy (Var x) = [x]
fvTyInTy (TCon _) = []
fvTyInTy (TArr t1 t2) = fvTyInTy t1 ++ fvTyInTy t2
fvTyInTy (TApp t1 (Right t2)) = fvTyInTy t1 ++ fvTyInTy t2
fvTyInTy (TApp t1 (Left  t2)) = fvTyInTy t1
fvTyInTy (TFix t) = fvTyInTy t
fvTyInTy _ = error "this should be unrechable for fvTyInTy" 

type Ctx = [(TmName,TySch)]
type TI = FreshMT (StateT [(TyName,Ki)]
                           (ErrorT UnifyError
                                   (State (UnificationState TyName Ty))))

type TySch = Bind [Either TmName TyName] Ty


kargs = unfoldr (\k -> case k of { KArr k1 k2 -> Just(k1,k2) ; _ -> Nothing })

arity nm kctx = length (kargs k)
   where Just k = lookup nm kctx

unfoldTArr (TArr t1 t2) = t1 : unfoldTArr t2
unfoldTArr ty           = [ty]

unfoldTApp (TApp t1 t2) = unfoldTApp t1 ++ [t2]
unfoldTApp ty           = [Right ty]

eitherVar = either (Left . Var) (Right . Var)


ti :: KCtx -> Ctx -> Ctx -> Env -> Tm -> TI Ty
ti kctx ictx ctx env (Var x)
       | head(show x) == '`' = throwError(strMsg $ show x++
                                 " backquoted variable not allowed (ti)")
ti kctx ictx ctx env (Var x) =
  case lookup x (ctx++ictx) of
    Just tysch -> return =<< freshTyInst tysch
    Nothing -> do
      ps <- lift get
      case lookup x ps of
        Just t -> return t
        Nothing -> throwError(strMsg $ show x++" undefined var")
ti kctx ictx ctx env (Con x) =
  case lookup x ictx of
    Just tysch -> return =<< freshTyInst tysch
    Nothing -> do
      ps <- lift get
      case lookup x ps of
        Just t -> return t
        Nothing -> throwError(strMsg $ show x++" undefined con")
ti kctx ictx ctx env e@(In m t)
  | m < 0     = throwError(strMsg $ show e ++ " has negative number")
  | otherwise =
    do ty <- ti kctx ictx ctx env t
              `catchErrorThrowWithMsg`
                 (++ "\n\t" ++ "when checking type of " ++ show t)
       let m_ = fromInteger m
       foldr mplus (throwError(strMsg $ show e ++ " has incorrect number")) $ do
         -- list monad (trying all combinations of Right and Left)
         mis <- sequence $ replicate m_ [ Right . Var <$> freshTyName' "t_InR_"
                                        , Left  . Var <$> freshTmName "i" Star]
         return $ do -- fresh monad
           is <- sequence mis
           ty1 <- Var <$> freshTyName' "t"
           lift2 $ unify (foldl TApp ty1 (Right (TFix ty1) : is)) ty
           return $ foldl TApp (TFix ty1) is
ti kctx ictx ctx env (MIt b) = trace (show (MIt b) ++ " %%%%%%%%%%%%%%%% ") $
  do (f, bb) <- unbind b
     cast <- fresh "cast"
     ti kctx ictx ctx env (MPr $ bind (f,cast) bb)
ti kctx ictx ctx env (MPr b) =
  do ((f,cast), Alt mphi as) <- unbind b
     k <- fresh "k"
     r <- freshTyName "_r" (Var k)
     t <- freshTyName' "t"
     mphi' <- freshenMPhi kctx ictx mphi
     (is, tyret) <- case mphi' of Nothing  -> (,) [] <$> (Var <$> freshTyName "_b" Star)
                                  Just phi -> do unbind (substBackquote env phi)
     let tyf    = foldl TApp (TCon r) (map eitherVar is) `TArr` tyret
     let tytm   = foldl TApp (Var t) (Right (TCon r) : map eitherVar is) `TArr` tyret
     let kctx' = (r, monoKi $ Var k) : kctx
     tyfsch <- case mphi' of
                 Nothing -> return (monoTy tyf)
                 _       ->
                   do (vs,_) <- unsafeUnbind <$> closeTy kctx' ictx tyret
                      psR <- sequence $ [(,) x <$> (Var <$> fresh "k") | Right x<-(is++vs)]
                      psL <- sequence $ [(,) x <$> (Var <$> freshTyName' "t") | Left x<-(is++vs)]
                      lift $ modify ((psL++psR)++)
                      () <- trace ("\tis = "++show is) $ return ()
                      () <- trace ("\tvs = "++show vs) $ return ()
                      () <- trace ("\ttyf = "++show tyf) $ return ()
                      return $ bind (union is vs) tyf
     let tycast = foldl TApp (TCon r) (map eitherVar is) `TArr`
                  foldl TApp (TFix (Var t)) (map eitherVar is)
     let ctx' = (f,tyfsch) : (cast,bind is tycast) : ctx
     () <- trace ("\tkctx' = "++show kctx') $ return ()
     () <- trace ("\tctx' = "++show ctx') $ return ()
     tytm' <- tiAlts 1 kctx' ictx ctx' env (Alt mphi' as)
     lift2 $ unify tytm tytm'
     u <- lift getSubst
     let ty = uapply u $
                foldl TApp (TFix(Var t)) (map eitherVar is) `TArr` tyret
     when (r `elem` fv ty) (throwError . strMsg $
             "abstract type variable "++show r++" cannot escape in type "++
             show ty ++" of "++show(MPr b) )
     return ty
ti kctx ictx ctx env (Lam b) =
  do (x, t) <- unbind b
     ty1 <- Var <$> freshTyName "_" Star
     ty2 <- ti kctx ictx ((x, monoTy ty1) : ctx) env t
     -- () <- trace ("\n\tkctx' = "++show kctx) $ return ()
     -- () <- trace ("\n\tictx' = "++show ictx) $ return ()
     ps <- get 
     () <- trace ("\n\tps = "++show ps) $ return ()
     lift2 . unify Star =<< ki kctx ictx env ty2
             `catchErrorThrowWithMsg`
                (++ "\n\t" ++ "when checking kind of " ++ show ty2
                 ++ "\n" ++ "kctx = " ++ show kctx
                 ++ "\n" ++ "ictx = " ++ show ictx
                 ++ "\n" ++ "ctx = " ++ show ((x, monoTy ty1) : ctx)
                 ++ "\n" ++ "env = " ++ show env
                )
     return (TArr ty1 ty2)
ti kctx ictx ctx env (App t1 t2) =
  do ty1 <- ti kctx ictx ctx env t1
             `catchErrorThrowWithMsg`
                (++ "\n\t" ++ "when checking type of " ++ show t1)
     ty2 <- ti kctx ictx ctx env t2
             `catchErrorThrowWithMsg`
                (++ "\n\t" ++ "when checking type of " ++ show t2
                 ++ "\n" ++ "kctx = " ++ show kctx
                 ++ "\n" ++ "ictx = " ++ show ictx
                 ++ "\n" ++ "ctx = " ++ show ctx
                )
     ty <- Var <$> freshTyName "a" Star
     lift2 $ unify (TArr ty2 ty) ty1
     return ty
ti kctx ictx ctx env (Let b) =
  do ((x, Embed t1), t2) <- unbind b
     ty <- ti kctx ictx ctx env t1
            `catchErrorThrowWithMsg`
               (++ "\n\t" ++ "when checking type of " ++ show t1)
     u <- lift getSubst
     tysch <- closeTy kctx (ictx++ctx) (uapply u ty)
     ti kctx ictx ((x, tysch) : ctx) env t2
ti kctx ictx ctx env (Alt _ []) = throwError(strMsg "empty Alts")
ti kctx ictx ctx env e@(Alt Nothing as) = tiAlts 0 kctx ictx ctx env e
ti kctx ictx ctx env (Alt (Just phi) as) =
  do phi <- freshenPhi kctx ictx phi
     tiAlts 0 kctx ictx ctx env (Alt (Just phi) as)


tiAlts n kctx ictx ctx env (Alt Nothing as) =  -- TODO coverage of all ctors
  do tys <- mapM (tiAlt kctx ictx ctx env Nothing) as
     lift2 $ unifyMany (zip tys (tail tys))
     return (head tys)
tiAlts n kctx ictx ctx env (Alt (Just phi) as) =  -- TODO coverage of all ctors
  do tys <- mapM (tiAlt kctx ictx ctx env (Just phi)) as
     u <- lift getSubst
     let (Right tcon : args) =
            tApp2list $ case (head tys) of TArr t _ -> uapply u t
     (is, rngty) <- unbind (substBackquote env phi)
     when (n + length is > length args)
        $ throwError(strMsg $ "too many indices in "++show phi)
     let args' = replaceSuffix args (map eitherVar is)
     let domty = foldl TApp tcon args'
     let tysch = bind is (TArr domty rngty)
     tys' <- mapM freshTyInst (replicate (length as) tysch)
     lift2 $ unifyMany (zip tys' tys)
     return =<< freshTyInst tysch


freshenPhi kctx ictx phi =
  do ((xs,ys),phi') <- unbind (bind (fvTmPhi,fvTyPhi) phi)
     psR <- sequence $ [(,) x <$> (Var <$> fresh "k_frPhiR_") | x<-ys]
     psL <- sequence $ [(,) x <$> (Var <$> freshTyName' "t_frPhiL_") | x<-xs]
     lift $ modify ((psL++psR)++)
     return phi'
  where
  (is,ty) = unsafeUnbind phi
  fvTmPhi = fvTmInTy ty \\ (fv is ++ fv kctx ++ fv ictx_)
  fvTyPhi = fvTyInTy ty \\ (fv is ++ fv kctx ++ fv ictx_)
  -- fvPhi = fv phi \\ (fv kctx ++ fv ictx_) :: [Name PSUT]
  ictx_ = filter (isUpper.head.show.fst) ictx

freshenMPhi kctx ictx Nothing    = return Nothing
freshenMPhi kctx ictx (Just phi) = Just <$> freshenPhi kctx ictx phi

replaceSuffix xs ys = reverse (drop (length ys) (reverse xs)) ++ ys

tApp2list (TApp ty1 targ) = tApp2list ty1 ++ [targ]
tApp2list ty             = [Right ty]

app2list (App t1 t2) = app2list t1 ++ [t2]
app2list t           = [t]


tiAlt kctx ictx ctx env mphi (x,b) =
  do xTy <- case lookup x ictx of
                 Nothing -> throwError . strMsg $ show x ++ " undefined"
                 Just xt -> freshTyInst xt
     u <- trace ("++++++++"++show x++"++++++++++++++\n"++show mphi++"\n xTy = "++show xTy) $ lift getSubst
     let xty = uapply u xTy
     let xtyUnfold = unfoldTArr xty
     let (xtyArgs, xtyRet) = (init xtyUnfold, last xtyUnfold)
     (u,is,bodyTy,mt) <- case trace (show(xty,xtyRet,mphi)) mphi of
        Nothing  -> return (u,[],undefined,Nothing)
        Just phi -> do
          (is, bodyTy) <- unbind phi
          psR <- sequence $ [(,) x <$> (Var <$> fresh "k_AltR_") | Right x<-is]
          psL <- sequence $ [(,) x <$> (Var <$> freshTyName' "_t") | Left x<-is]
          lift $ modify ((psL++psR)++)
          t <- Var <$> freshTyName' "t"
          lift2 $ unify (foldl TApp t $ map eitherVar is) xtyRet
          u <- lift getSubst
          let bodyTy' = uapply u bodyTy
          return (u,is,bodyTy',Just t)
     let xty_ = uapply u xty
     let xty = case trace ("xty_ = "++show xty_) () of _ -> xty_
     let xtyUnfold = unfoldTArr xty
     let (xtyArgs, xtyRet) = (init xtyUnfold, last xtyUnfold)
     let xTyVars = nub $ (fv xty \\ fvTmInTy xty)
                      \\ (fv kctx ++ fv ictx ++ fv ctx)
     let xTmVars = nub $ (fvTmInTy xty \\ fv xtyRet)
                      \\ (fv kctx ++ fv ictx ++ fv ctx)
     let eTyVars = xTyVars \\ fv xtyRet
     let eTmVars = xTmVars \\ fv xtyRet

     () <- trace ("evars : "++show(eTyVars,eTmVars)) $ return ()

     let ictx_ = filter (isUpper.head.show.fst) ictx
     let fvTyPhi = case mt of
                     Nothing -> []
                     Just _  -> nub $ (fv bodyTy \\ fv is) \\ (fv kctx ++ fv ictx_ ++ fvTmInTy bodyTy)
         fvTmPhi = case mt of
                     Nothing -> []
                     Just _  -> nub $ (fvTmInTy bodyTy \\ fv is) \\ (fv kctx ++ fv ictx_)

     -- substitute existential vars as bogus TCon or Con to avoid unification
     -- TODO generalized existentials???
     let xty' = foldr (.) id
                    (  [LN.subst nm (TCon nm) | nm <- eTyVars] 
                    ++ [LN.subst nm (Con nm)  | nm <- eTmVars] ) xty
     () <- trace ("TODO " ++ show(ty2Type xty')) $ return () 
     let bodyTy' = foldr (.) id
                    (  [LN.subst nm (TCon nm) | nm <- eTyVars] 
                    ++ [LN.subst nm (Con nm)  | nm <- eTmVars] ) bodyTy
     let xtyArgs' = trace (show (xty',init (unfoldTArr xty'))) $ init (unfoldTArr xty')
     let kctx' = kctx
     let ictx' = ictx
     -- -- adding existental TCon or Con to context seems unnecessary
     -- kctx' <- (++) <$> sequence [(,) nm <$> (Var <$> fresh "k") | nm <- eTyVars]
     --               <*> return kctx
     -- ictx' <- (++) <$> sequence [(,) nm <$> (monoTy . Var <$> fresh "c")
     --                             | nm <- eTmVars]
     --               <*> return ictx
     (ns,t) <- unbind b
     let ctx' = trace (show ns ++", "++ show xtyArgs') $ zip ns (map monoTy xtyArgs') ++ ctx
     () <- trace "zzaaa" $ return ()
     domty <- ti kctx' ictx' ctx' env (foldl1 App (Con x : map Var ns))
              `catchErrorThrowWithMsg`
                 (++ "\n\t" ++ "when checking type of "
                  ++ show (foldl1 App (Con x : map Var ns)))
     rngty <- ti kctx' ictx' ctx' env t
              `catchErrorThrowWithMsg`
                 (++ "\n\t" ++ "when checking type of " ++ show t)
     () <- trace ("zzaaa2\t"++show xtyRet++" =?= "++show domty) $ return ()
     lift2 $ unify xtyRet domty
     () <- trace "zzaaa3" $ return ()
     u <- lift getSubst
     case mt of
       Nothing  -> return ()
       Just _   ->
                do () <- trace ("zzaaa4\t"++
                                show bodyTy'++" =?= "++show rngty) $ return ()
                   lift2 $ unify bodyTy' rngty
     u <- lift getSubst
     () <- trace "zzaaa5" $ return ()
     let ty = uapply u (TArr domty rngty)
     let TArr domty rngty = ty
     let eRetVars = intersect (eTyVars ++ eTmVars) (fv ty)
     unless (trace (show(ty,eRetVars)) $ null eRetVars)
            (throwError . strMsg $ "rigid variables "++ show eRetVars ++
                                   " in the return type "++ show rngty ++
                                   " of "++ show t)
     u <- lift getSubst
     unless (null $ filter (\(x,t)-> elem x (fvTyPhi ++ fvTmPhi)
                                  && case t of {Var _ -> False; _ -> True}) u)
       (throwError . strMsg $ "polymorphic vars in phi cannot be specialized "
             ++"\n\t"
             ++show(filter (\(x,t)-> elem x (fvTyPhi ++ fvTmPhi)
                                  && case t of {Var _ -> False; _ -> True}) u))
     case mphi of
       Nothing -> trace
                    ("return type: "++show ty ++ "\n"++
                     show(eTyVars++eTmVars::[TyName]
                         ,fv xtyRet::[TyName]
                         ,(eTyVars++eTmVars)\\fv xtyRet::[TyName])
                     ++
                     "\n\t"++ show(eTyVars++eTmVars)++" of "++show xtyRet
                           ++ show(fv xtyRet::[TyName])++" in "++show (x,b))
                    (return ty)
       Just phi -> do
         let Just t = trace
                        ("return type: "++show ty ++ "\n"++
                         show(eTyVars++eTmVars::[TyName]
                             ,fv xtyRet::[TyName]
                             ,(eTyVars++eTmVars)\\fv xtyRet::[TyName])
                         ++
                         "\n\t"++ show(eTyVars++eTmVars)++" of "++show xtyRet
                               ++ show(fv xtyRet::[TyName])++" in "++show (x,b))
                        mt
         let t' = uapply u t
         (is,bodyTy) <- unbind phi
         let bodyTy' = uapply u bodyTy
         return (foldl TApp t' (map eitherVar is) `TArr` bodyTy')
  -- catching error from do ...
  `catchErrorThrowWithMsg` (++ "\n\t" ++ "when checking case " ++ show x)



lam x t = Lam (bind x t)

idTm = lam "x" (Var "x")

nullState = UState [] []


-- runUS = runUSwith nullState

runUSwith st0 st = fst (runState st st0)
                   -- uapply (uSubst s) e where (e,s) = runState st st0

runTI = runTIwith nullState []
 
runTIwith stUS st = runUSwith stUS . runErrorT . flip evalStateT st . runFreshMT


ti' ctx = runTI . ti [] [] [] ctx

ty = runTI $ ti [] [] [] [] (lam "x" (Var "x"))


unbindSch sch = snd (unsafeUnbind sch)

monoKi = bind ([],[],[])
monoTy = bind []

-- evaluation

type Env = [(TmName,Tm)]

sreturn env t = return $ foldr (.) id (map (uncurry LN.subst) env) t

ev env (Var x)
  | head(show x) == '`' = throwError(strMsg $ show x++
                                     " backquoted variable not allowed (ev)")
ev env (Var x) =
  case lookup x env of
    Nothing -> throwError(strMsg $ show x++" undefined")
    Just v  -> return v
ev env v@(Con x) = return v
ev env (In n t) = In n <$> ev env t
ev env v@(MIt b) = return v
ev env v@(MPr b) = return v
ev env v@(Lam b) = return v
ev env (App t1 t2) =
  do v1 <- ev env t1
     v2 <- ev env t2
     case v1 of
       Var x -> error $ show x ++ " (free variable): should never happen"
       Con _ -> return $ App v1 v2
       In _ _ -> return $ App v1 v2
       App _ _ -> return $ App v1 v2
       Lam b -> do (x, t) <- unbind b
                   let env' = (x,v2) : env
                   sreturn [(x,v2)] =<< ev env' t
       MIt b -> do (f,t) <- unbind b
                   let env' = (f,v1) : env
                   let In _ v = v2
                   sreturn [(f,v1)] =<< ev env' (App t v)
       MPr b -> do ((f,cast),t) <- unbind b
                   let env' = (f,v1) : (cast,idTm) : env
                   let In _ v = v2
                   sreturn [(f,v1),(cast,idTm)] =<< ev env' (App t v)
       Alt m as ->
         do let (Con c:vs) = app2list v2
            case lookup c as of
              Nothing -> throwError(strMsg $ show c++" undefined")
              Just b  ->
                do (xs,t) <- unbind b
                   let env' = zip xs vs ++ env
                   sreturn (zip xs vs) =<< ev env' t
ev env (Let b) = do ((x, Embed t1), t2) <- unbind b
                    v1 <- ev env t1
                    let env' = (x,v1) : env
                    sreturn [(x,v1)] =<< ev env' t2
ev env v@(Alt _ _) = return v



norm env Star = return Star
norm env (KArr (Right k1) k2) = KArr <$> (Right <$> norm env k1) <*> norm env k2
norm env (KArr (Left  t1) k2) = KArr <$> (Left  <$> norm env t1) <*> norm env k2
norm env t@(TCon _) = return t
norm env (TArr t1 t2) = TArr <$> norm env t1 <*> norm env t2
norm env (TApp t1 (Right t2)) = TApp <$> norm env t1 <*> (Right <$> norm env t2)
norm env (TApp t1 (Left  e2)) = TApp <$> norm env t1 <*> (Left  <$> norm env e2)
norm env (TFix t) = TFix <$> norm env t
norm env v@(Var x)
  | head(show x) == '`' = throwError(strMsg $ show x++
                                     " backquoted variable not allowed (norm)")
norm env v@(Var x) =
  case lookup x env of
    Nothing -> return v
    Just v  -> return v
norm env v@(Con x) = return v
norm env (In n t) = In n <$> norm env t
norm env (MIt b) = do (xs,t) <- unbind b
                      MIt <$> (bind xs <$> norm env t)
norm env (MPr b) = do (xs,t) <- unbind b
                      MPr <$> (bind xs <$> norm env t)
norm env (Lam b) = do (x, t) <- unbind b
                      Lam . bind x <$> norm env t
norm env (App t1 t2) =
  do v1 <- norm env t1
     v2 <- norm env t2
     case v1 of
       Var x -> return $ App v1 v2
       Con _ -> return $ App v1 v2
       In _ _ -> return $ App v1 v2
       App _ _ -> return $ App v1 v2
       Lam b ->
         do (x, t) <- unbind b
            let env' = (x,v2) : env
            sreturn [(x,v2)] =<< norm env' t
       MIt b ->
         do (f,t) <- unbind b
            let env' = (f,v1) : env
            case v2 of
              In _ v -> sreturn [(f,v1)] =<< norm env' (App t v)
              _      -> return (App v1 v2)
       MPr b ->
         do ((f,cast),t) <- unbind b
            let env' = (f,v1) : (cast,idTm) : env
            case v2 of
              In _ v -> sreturn [(f,v1),(cast,idTm)] =<< norm env' (App t v)
              _      -> return (App v1 v2)
       Alt m as ->
         do let (Con c:vs) = app2list v2
            case lookup c as of
              Nothing -> throwError(strMsg $ show c++" undefined")
              Just b  ->
                do (xs,t) <- unbind b
                   let env' = zip xs vs ++ env
                   sreturn (zip xs vs) =<< norm env' t
norm env (Let b) = do ((x, Embed t1), t2) <- unbind b
                      v1 <- norm env t1
                      let env' = (x,v1) : env
                      sreturn [(x,v1)] =<< norm env' t2
norm env (Alt m as) =
  Alt m <$> sequence [ do (xs,t) <- unbind b
                          (,) c <$> (bind xs <$> norm env t)
                      | (c,b) <- as ]

