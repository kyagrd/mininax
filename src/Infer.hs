-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE TemplateHaskell,
             MultiParamTypeClasses,
             FlexibleInstances,
             FlexibleContexts,
             OverlappingInstances,
             IncoherentInstances,
             OverloadedStrings,
             GADTs,
             NoMonomorphismRestriction,
             ScopedTypeVariables,
             CPP #-}

module Infer where

import Syntax

import Data.Char
import Data.List
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Error
import Control.Monad.State
import Language.LBNF.Runtime
import Parser (ty2Type)
import Generics.RepLib.Unify hiding (solveUnification)
import Unbound.LocallyNameless hiding (subst, Con)
import qualified Unbound.LocallyNameless as LN
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import GHC.Exts( IsString(..) )
-- import Debug.Trace
trace _ a = a

catchErrorThrowWithMsg m f = m `catchError` (\e -> throwError . strMsg $ f e)


instance HasVar (Name PSUT) PSUT where
  is_var (Var nm) = Just nm
  is_var _ = Nothing
  var = Var

instance (Eq n, Show n, Show a, HasVar n a) => Unify n a String where
   unifyStep _ = unifyStepEq

instance (Eq n, Show n, Show a, HasVar n a) => Unify n a (Name s) where
   unifyStep _ = unifyStepEq

instance ( Alpha n, Eq n, Show n, HasVar n PSUT) => Unify n PSUT (Bind n PSUT) where
   unifyStep _ b1 b2 
       | b1 `aeq` b2 = return ()
       | otherwise   =
           do (e1,e2) <- runFreshMT $
                         do { (_,e1) <- unbind b1
                            ; (_,e2) <- unbind b2
                            ; return (e1,e2) }
              trace ("trace in instance Unify n a (Bind n a): " ++ show (e1,e2)) $
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
     r >> return (uSubst final)
     -- case r of Left e  -> throwError e
     --           Right _ -> return $ uSubst final
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

{-
solveUnification (eqs :: [(PSUT, PSUT)]) =
     r >> return (uSubst final)
     -- case r of Left e  -> throwError e
     --           Right _ -> return $ uSubst final
     where
     (r, final) = runState (runErrorT rwConstraints) (UState cs [])
     cs = do (a1, a2) <- eqs
             let (a1',a2') | isTm a1 && isTm a2
                                       = ( runEither . runFreshMT $ norm [] a1
                                         , runEither . runFreshMT $ norm [] a2 )
                           | otherwise = (a1, a2)
                 
             return (UC dict a1' a2')
     rwConstraints :: UM (Name PSUT) PSUT ()
     rwConstraints =
       do c <- dequeueConstraint
          case c of Just (UC d a1 a2) ->
                            do unifyStepD d (undefined :: Proxy (Name PSUT, PSUT)) a1 a2
                               rwConstraints
                    Nothing -> return ()


runEither (Right a) = a
runEither (Left b) = error b
-}

-- Don't know why but sometimes have to manually inline this.
-- Myabe because of some dictionary passing craziness on subst???
uapply s = foldr (.) id (map (uncurry subst) $ reverse s)
-- {-# INLINE uapply #-}

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


getSubst = do { UState _ s <- lift get; return s }
putSubst u = do { UState c s <- lift get; lift $ put (UState c s); return () }

extendSubst (x,Var y) | y < x = extendSubst (y,Var x)
extendSubst (x,t) =
  do u <- getSubst
     case lookup x u of
       Nothing -> extendSubstitution (x,t)
       Just t' -> unify t t' >> extendSubstitution (x,t)


unify t1 t2 = trace ("unify ("++show t1++") ("++show t2++")") (mapM_ extendSubst =<< mgu t1 t2)

unifyMany ps = mapM_ extendSubst =<< mguMany ps


type KCtx = [(TyName,KiSch)]
type KI = FreshMT (ErrorT UnifyError (State (UnificationState KiName Ki)))

type KiSch = Bind ([TmName],[TyName],[KiName]) Ki

ki :: KCtx -> Ctx -> Env -> Ty -> KI Ki
ki kctx ictx env (Var x)
   | head(show x) == '`' = throwError(strMsg $ show x++
                                      " backquoted variable not allowed (ki)")
ki kctx ictx env (Var x) =
  case lookup x kctx of
    Nothing -> throwError(strMsg $ "ty var "++show x++" undefined tyvar")
    Just kisch -> return =<< freshInst kisch -- ki vars should be simple though
ki kctx ictx env (TCon x) =
  case lookup x kctx of
    Nothing -> throwError(strMsg $ "ty con "++show x++" undefined tycon")
    Just kisch -> return =<< freshInst kisch
ki kctx ictx env (TArr t1 t2) =
  do k1 <- ki kctx ictx env t1
     k2 <- ki kctx ictx env t2
     lift $ unify Star k1
     lift $ unify Star k2
     return Star
ki kctx ictx env (TApp t1 (Right t2)) =
  do k1 <- ki kctx ictx env t1
     k2 <- ki kctx ictx env t2
     k <- Var <$> fresh "k"
     lift $ unify (KArr (Right k2) k) k1
     return k
ki kctx ictx env (TApp t1 (Left e2)) =
  do k1 <- ki kctx ictx env t1
     t2 <- ti kctx ictx [] env e2
     k <- Var <$> fresh "k"
     lift $ unify (KArr (Left t2) k) k1
     return k
ki kctx ictx env (TFix t) =
  do k1 <- ki kctx ictx env t
     k <- Var <$> fresh "k"
     lift $ unify (KArr (Right k) k) k1
     return k

freshInst sch = liftM snd (unbind sch)


closeKi kctx ctx as k = do -- as are extra vars that should not to generalize
  () <- trace ("closeKi "++show k
                     ++"\n\t"++show freeKiVars
                     ++"\n\t"++show freeTyVars
                     ++"\n\t"++show freeTmVars) $ return ()
  () <- trace ("\n\t freeKiVars = "++show freeKiVars
             ++"\n\t freeNonKiVars = "++show freeNonKiVars
             ++"\n\t freeTyVars = "++show freeTyVars
             ++"\n\t freeTmVars = "++show freeTmVars ) $ return ()
  () <- trace ("\n\t kctx = "++show kctx
             ++"\n\t ctx = "++show ctx ) $ return ()
  () <- trace ("\n\t fv k = "++show(fv k::[KiName])) $ return ()
  return $ bind (freeKiVars,freeTyVars,freeTmVars) k
  where
  freeKiVars = nub (fvKi k) \\ (fv ctx ++ fv kctx ++ as)
  freeNonKiVars = nub (concatMap fv $ tysInKi k)
                  \\ (fv ctx ++ fv kctx ++ freeKiVars ++ as)
  freeTyVars = freeNonKiVars \\ freeTmVars
  freeTmVars = nub (concatMap fvTmInTy $ tysInKi k) \\ (fv ctx ++ fv kctx ++ as)


closeTy kctx ctx ty = do
  return $ bind (map Right freeRvars ++ map Left freeLvars) ty
  where
  freevars = nub (fv ty) \\ (fv ctx ++ fv kctx)
  freeLvars = nub (fvTmInTy ty) \\ (fv ctx ++ fv kctx)
  freeRvars = freevars \\ freeLvars


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

type Ctx = [(TmName,TySch)]
type TI = FreshMT (ErrorT UnifyError (State (UnificationState TyName Ty)))

type TySch = Bind [Either TmName TyName] Ty


kargs = unfoldr (\k -> case k of { KArr k1 k2 -> Just(k1,k2) ; _ -> Nothing })

arity nm kctx = length (kargs k)
   where Just k = lookup nm kctx

unfoldTArr (TArr t1 t2) = t1 : unfoldTArr t2
unfoldTArr ty           = [ty]

unfoldTApp (TApp t1 t2) = unfoldTApp t1 ++ [t2]
unfoldTApp ty           = [Right ty]


eitherVar = either (Left . Var) (Right . Var)

-- ureturn ty = do { u <- getSubst; return (uapply u ty) }

-- TODO catch errors and append more context info in error msg
ti :: KCtx -> Ctx -> Ctx -> Env -> Tm -> TI Ty
ti kctx ictx ctx env (Var x)
       | head(show x) == '`' = throwError(strMsg $ show x++
                                          " backquoted variable not allowed (ti)")
ti kctx ictx ctx env (Var x) =
  case lookup x (ctx++ictx) of
    Nothing -> throwError(strMsg $ show x++" undefined var")
    Just tysch -> return =<< freshInst tysch
ti kctx ictx ctx env (Con x) =
  case lookup x ictx of
    Nothing -> throwError(strMsg $ show x++" undefined con")
    Just tysch -> return =<< freshInst tysch
ti kctx ictx ctx env e@(In n t)
  | n < 0     = throwError(strMsg $ show e ++ " has negative number")
  | otherwise =
    do ty <- ti kctx ictx ctx env t
       let m = fromInteger n
       foldr mplus (throwError(strMsg $ show e ++ " has incorrect number")) $ do
         -- list monad (trying all combinations of Right and Left)
         mis <- sequence $ replicate m [ Right . Var <$> fresh "k"
                                       , Left  . Var <$> fresh "i" ]
         return $ do -- fresh monad
           is <- sequence mis
           ty1 <- Var <$> fresh "t"
           lift $ unify (foldl TApp ty1 (Right (TFix ty1) : is)) ty
           return $ foldl TApp (TFix ty1) is
ti kctx ictx ctx env (MIt b) = trace (show (MIt b) ++ " %%%%%%%%%%%%%%%% ") $
  do (f, Alt mphi as) <- unbind b
     r <- fresh "_r"
     t <- fresh "t"
     mphi' <- freshenMPhi kctx ictx mphi
     (is, tyret) <- case mphi' of Nothing  -> (,) [] <$> (Var <$> fresh "b_")
                                  Just phi -> do unbind (substBackquote env phi)
     let tyf  = foldl TApp (TCon r) (map eitherVar is) `TArr` tyret
     let tytm = foldl TApp (Var t) (Right (TCon r) : map eitherVar is) `TArr` tyret
     k <- fresh "k"
     let kctx' = (r, monoKi $ Var k) : kctx
     let ctx' = (f,bind is tyf) : ctx
     () <- trace ("\tkctx' = "++show kctx') $ return ()
     () <- trace ("\tctx' = "++show ctx') $ return ()
     tytm' <- tiAlts kctx' ictx ctx' env (Alt mphi' as)
     lift $ unify tytm tytm'
     u <- getSubst
     let ty = uapply u $
                foldl TApp (TFix(Var t)) (map eitherVar is) `TArr` tyret
     when (r `elem` fv ty) (throwError . strMsg $
             "abstract type variable "++show r++" cannot escape in type "++
             show ty ++" of "++show(MIt b) )
     return ty
ti kctx ictx ctx env (MPr b) =
  do ((f,cast), Alt mphi as) <- unbind b
     r <- fresh "_r"
     t <- fresh "t"
     k <- fresh "k"
     mphi' <- freshenMPhi kctx ictx mphi
     (is, tyret) <- case mphi' of Nothing  -> (,) [] <$> (Var <$> fresh "_b")
                                  Just phi -> do unbind (substBackquote env phi)
     let tyf    = foldl TApp (TCon r) (map eitherVar is) `TArr` tyret
     let tycast = foldl TApp (TCon r) (map eitherVar is) `TArr`
                  foldl TApp (TFix (Var t)) (map eitherVar is)
     let tytm   = foldl TApp (Var t) (Right (TCon r) : map eitherVar is)
                  `TArr` tyret
     let kctx' = (r, bind ([],[],[]) $ Var k) : kctx
     let ctx' = (f,bind is tyf) : (cast,bind is tycast) : ctx
     tytm' <- tiAlts kctx' ictx ctx' env (Alt mphi' as)
     lift $ unify tytm tytm'
     u <- getSubst
     let ty = uapply u $
                foldl TApp (TFix(Var t)) (map eitherVar is) `TArr` tyret
     when (r `elem` fv ty) (throwError . strMsg $
             "abstract type variable "++show r++" cannot escape in type "++
             show ty ++" of "++show(MPr b) )
     return ty
ti kctx ictx ctx env (Lam b) =
  do (x, t) <- unbind b
     ty1 <- Var <$> fresh "_"
     ty2 <- ti kctx ictx ((x, monoTy ty1) : ctx) env t
     return (TArr ty1 ty2)
ti kctx ictx ctx env (App t1 t2) =
  do ty1 <- ti kctx ictx ctx env t1
             `catchErrorThrowWithMsg`
                 (++ "\n\t" ++ "when checking type of " ++ show t1)
     ty2 <- ti kctx ictx ctx env t2
             `catchErrorThrowWithMsg`
                 (++ "\n\t" ++ "when checking type of " ++ show t1)
     ty <- Var <$> fresh "a"
     lift $ unify (TArr ty2 ty) ty1
     return ty
ti kctx ictx ctx env (Let b) =
  do ((x, Embed t1), t2) <- unbind b
     ty <- ti kctx ictx ctx env t1
     u <- getSubst
     tysch <- closeTy kctx (ictx++ctx) (uapply u ty)
     ti kctx ictx ((x, tysch) : ctx) env t2
ti kctx ictx ctx env (Alt _ []) = throwError(strMsg "empty Alts")
ti kctx ictx ctx env e@(Alt Nothing as) = tiAlts kctx ictx ctx env e
ti kctx ictx ctx env (Alt (Just phi) as) =
  do phi <- freshenPhi kctx ictx phi
     tiAlts kctx ictx ctx env (Alt (Just phi) as)


tiAlts kctx ictx ctx env (Alt Nothing as) =  -- TODO coverage of all ctors
  do tys <- mapM (tiAlt kctx ictx ctx env Nothing) as
     lift $ unifyMany (zip tys (tail tys))
     return (head tys)
tiAlts kctx ictx ctx env (Alt (Just phi) as) =  -- TODO coverage of all ctors
  do tys <- mapM (tiAlt kctx ictx ctx env (Just phi)) as
     u <- getSubst
     let (Right tcon : args) =
            tApp2list $ case (head tys) of TArr t _ -> uapply u t
     (is, rngty) <- unbind (substBackquote env phi)
     when (1 + length is > length args)
        $ throwError(strMsg $ "too many indices in "++show phi)
     let args' = replaceSuffix args (map eitherVar is)
     let domty = foldl TApp tcon args'
     let tysch = bind is (TArr domty rngty)
     tys' <- mapM freshInst (replicate (length as) tysch)
     lift $ unifyMany (zip tys' tys)
     return =<< freshInst tysch


freshenPhi kctx ictx phi = snd <$> unbind (bind fvPhi phi)
  where
  fvPhi = fv phi \\ (fv kctx ++ fv ictx_) :: [Name PSUT]
  ictx_ = filter (isUpper.head.show.fst) ictx

freshenMPhi kctx ictx Nothing    = return Nothing
freshenMPhi kctx ictx (Just phi) = Just <$> freshenPhi kctx ictx phi

replaceSuffix xs ys = reverse (drop (length ys) (reverse xs)) ++ ys

tApp2list (TApp ty1 targ) = tApp2list ty1 ++ [targ]
tApp2list ty             = [Right ty]

app2list (App t1 t2) = app2list t1 ++ [t2]
app2list t           = [t]


{-
 (is,body) <- unbind phi
     let ictx_ = filter (isUpper.head.show.fst) ictx
     let fvTyPhi = nub $ (fv body \\ fv is) \\ (fv kctx ++ fv ictx_ ++ fvTmInTy body)
         fvTmPhi = nub $ (fvTmInTy body \\ fv is) \\ (fv kctx ++ fv ictx_)
     kctx' <- (++ kctx) <$>
                 sequence [ (,) x <$> (Var <$> fresh "k") | x <- fvTyPhi ]
     ictx' <- (++ ictx) <$>
                 sequence [ (,) x <$> (monoTy <$> (Var <$> fresh "c")) | x <- fvTmPhi ]
-}


tiAlt kctx ictx ctx env mphi (x,b) =
  do xTy <- case lookup x ictx of
                 Nothing -> throwError . strMsg $ show x ++ " undefined"
                 Just xt -> freshInst xt
     u <- trace ("++++++++"++show x++"++++++++++++++\n"++show mphi++"\n xTy = "++show xTy) $ getSubst
     let xty = uapply u xTy
     let xtyUnfold = unfoldTArr xty
     let (xtyArgs, xtyRet) = (init xtyUnfold, last xtyUnfold)
     (u,is,bodyTy,mt) <- case trace (show(xty,xtyRet,mphi)) mphi of
        Nothing  -> return (u,[],undefined,Nothing)
        Just phi -> do
          (is, bodyTy) <- unbind phi
          t <- (Var <$> fresh "t")
          lift $ unify (foldl TApp t $ map eitherVar is) xtyRet
          u <- getSubst
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
                 (++ "\n\t" ++ "when checking type of " ++ show (foldl1 App (Con x : map Var ns)))

     rngty <- ti kctx' ictx' ctx' env t
              `catchErrorThrowWithMsg`
                 (++ "\n\t" ++ "when checking type of " ++ show t)
     () <- trace ("zzaaa2\t"++show xtyRet++" =?= "++show domty) $ return ()
     lift $ trace "aaaaaa" $ unify xtyRet (trace "AAAA " domty)
     () <- trace "zzaaa3" $ return ()
     u <- getSubst
     case mt of
       Nothing  -> return ()
       Just _   ->
                do () <- trace ("zzaaa4\t"++
                                show bodyTy'++" =?= "++show rngty) $ return ()
                   lift $ unify bodyTy' rngty
     u <- getSubst
     () <- trace "zzaaa5" $ return ()
     let ty = uapply u (TArr domty rngty)
     let TArr domty rngty = ty
     let eRetVars = intersect (eTyVars ++ eTmVars) (fv ty)
     unless (trace (show(ty,eRetVars)) $ null eRetVars)
            (throwError . strMsg $ "rigid variables "++ show eRetVars ++
                                   " in the return type "++ show rngty ++
                                   " of "++ show t)
     u <- getSubst
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




_x = "x"
x = Var _x
_y = "y"
y = Var _y

lam x t = Lam (bind x t)

nullState = UState [] []


runUS = runUSwith nullState

runUSwith st0 st = uapply (uSubst s) e where (e,s) = runState st st0


runTI = runTIwith nullState

runTIwith st = runUSwith st . runErrorT . runFreshMT

ti' ctx = runTI . ti [] [] [] ctx

ty = runTI $ ti [] [] [] [] (lam _x x)


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
                   let env' = (f,v1) : (cast,lam _x x) : env
                   let In _ v = v2
                   sreturn [(f,v1),(cast,lam _x x)] =<< ev env' (App t v)
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
            let env' = (f,v1) : (cast,lam _x x) : env
            case v2 of
              In _ v -> sreturn [(f,v1),(cast,lam _x x)] =<< norm env' (App t v)
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

