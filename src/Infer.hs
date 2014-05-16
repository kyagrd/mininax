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

import Data.List
import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Error
import Control.Monad.State
import Language.LBNF.Runtime
import Parser ()
import Generics.RepLib.Unify hiding (solveUnification)
import Unbound.LocallyNameless hiding (subst, Con)
import qualified Unbound.LocallyNameless as LN
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import GHC.Exts( IsString(..) )
-- import Debug.Trace
trace _ a = a

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



-- Don't know why but sometimes have to manually inline this.
-- Myabe because of some dictionary passing craziness on subst???
uapply s = foldr (.) id (map (uncurry subst) s)

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

extendSubst (x,t) =
  do u <- getSubst
     case lookup x u of
       Nothing -> extendSubstitution (x,t)
       Just t' -> unify t t' >> extendSubstitution (x,t)


unify t1 t2 = mapM_ extendSubst =<< mgu t1 t2

unifyMany ps = mapM_ extendSubst =<< mguMany ps


type KCtx = [(TyName,Ki)]
type KI = FreshMT (ErrorT UnifyError (State (UnificationState KiName Ki)))


ki :: KCtx -> Ctx -> Ty -> KI Ki
ki kctx ictx (Var x) =
  case lookup x kctx of
    Nothing -> throwError(strMsg $ "ty var "++name2String x++" undefined")
    Just k -> return k -- currently just simple kinds
ki kctx ictx (TCon x) =
  case lookup x kctx of
    Nothing -> throwError(strMsg $ "ty con "++name2String x++" undefined")
    Just k -> return k -- currently just simple kinds
ki kctx ictx (TArr t1 t2) =
  do k1 <- ki kctx ictx t1
     k2 <- ki kctx ictx t2
     lift $ unify Star k1
     lift $ unify Star k2
     return Star
ki kctx ictx (TApp t1 (Right t2)) =
  do k1 <- ki kctx ictx t1
     k2 <- ki kctx ictx t2
     k <- Var <$> fresh "k"
     lift $ unify (KArr (Right k2) k) k1
     return k
ki kctx ictx (TApp t1 (Left e2)) =
  do k1 <- ki kctx ictx t1
     t2 <- ti kctx ictx [] e2
     k <- Var <$> fresh "k"
     lift $ unify (KArr (Left t2) k) k1
     return k
ki kctx ictx (TFix t) =
  do k1 <- ki kctx ictx t
     k <- Var <$> fresh "k"
     lift $ unify (KArr (Right k) k) k1
     return k


freshInst tysch = liftM snd (unbind tysch)

-- closeTy :: KCtx -> Ctx -> Ty -> TySch
closeTy kctx ctx ty = do
  return $ bind (map Right freeRvars ++ map Left freeLvars) ty
  where
  freevars = nub (fv ty) \\ (fv ctx ++ fv kctx)
  freeLvars = nub (fvTmInTy ty) \\ (fv ctx ++ fv kctx)
  freeRvars = freevars \\ freeLvars

-- sorry no generic programming in here :( TODO is there a way?
fvTmInTy t | not(isTy t) = []
fvTmInTy (Var _) = []
fvTmInTy (TCon _) = []
fvTmInTy (TArr t1 t2) = fvTmInTy t1 ++ fvTmInTy t2
fvTmInTy (TApp t1 (Right t2)) = fvTmInTy t1 ++ fvTmInTy t2
fvTmInTy (TApp t1 (Left  t2)) = fvTmInTy t2 ++ fv t2
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




-- We need to examine how many parameters a fixpoint can have
-- To do so we must find index to the first argument r.
-- First need to know the kind of r, and the arity of the kind ???
-- But here we just have a hacky implementation, which I am
-- not 100% sure of it correctness. Seem to work for now :(
--
-- arityParam nm kctx ctx
--    length (kargs k)
--    where Just k = lookup nm kctx


-- ureturn ty = do { u <- getSubst; return (uapply u ty) }
-- ureturn ty = do { u <- getSubst; return (foldr (.) id (map (uncurry subst) u) ty) }

-- TODO catch errors and append more context info
ti :: KCtx -> Ctx -> Ctx -> Tm -> TI Ty
ti kctx ictx ctx (Var x) =
  case lookup x (ctx++ictx) of
    Nothing -> throwError(strMsg $ name2String x++" undefined")
    Just tysch -> return =<< freshInst tysch
ti kctx ictx ctx (Con x) =
  case lookup x ictx of
    Nothing -> throwError(strMsg $ name2String x++" undefined")
    Just tysch -> return =<< freshInst tysch
-- TODO term index
ti kctx ictx ctx e@(In n t) -- this is a hacky implementation without checking kinds
  | n < 0     = throwError(strMsg $ show e ++ " has negative number")
  | otherwise =
    do ty <- ti kctx ictx ctx t
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
ti kctx ictx ctx (MIt b) =
  do (f,tm@(Alt mphi as)) <- unbind b
     r <- fresh "_r"
     t <- fresh "t"
     (is, tyret) <- case mphi of Nothing  -> (,) [] <$> (Var <$> fresh "b")
                                 Just phi -> unbind phi
     let tyf  = foldl TApp (TCon r) (map eitherVar is) `TArr` tyret
     let tytm = foldl TApp (Var t) (Right (TCon r) : map eitherVar is) `TArr` tyret
     k <- fresh "k"
     let kctx' = (r, Var k) : kctx
     let ctx' = (f,bind is tyf) : ctx
     tytm' <- ti kctx' ictx ctx' tm
     lift $ unify tytm tytm'
     u <- getSubst
     let ty = foldr (.) id (map (uncurry subst) u) $
               foldl TApp (TFix(Var t)) (map eitherVar is) `TArr` tyret
     when (r `elem` fv ty) (throwError . strMsg $
             "abstract type variable "++show r++" cannot escape in type "++
             show ty ++" of "++show(MIt b) )
     return ty
   where
   eitherVar = either (Left . Var) (Right . Var)
ti kctx ictx ctx (MPr b) =
  do ((f,cast),tm@(Alt mphi as)) <- unbind b
     r <- fresh "_r"
     t <- fresh "t"
     k <- fresh "k"
     (is, tyret) <- case mphi of Nothing  -> (,) [] <$> (Var <$> fresh "b")
                                 Just phi -> unbind phi
     let tyf    = foldl TApp (TCon r) (map eitherVar is) `TArr` tyret
     let tycast = foldl TApp (TCon r) (map eitherVar is) `TArr`
                  foldl TApp (TFix (Var t)) (map eitherVar is)
     let tytm   = foldl TApp (Var t) (Right (TCon r) : map eitherVar is) `TArr` tyret
     let kctx' = (r, Var k) : kctx
     let ctx' = (f,bind is tyf) : (cast,bind is tycast) : ctx
     tytm' <- ti kctx' ictx ctx' tm
     lift $ unify tytm tytm'
     u <- getSubst
     let ty = foldr (.) id (map (uncurry subst) u) $
               foldl TApp (TFix(Var t)) (map eitherVar is) `TArr` tyret
     when (r `elem` fv ty) (throwError . strMsg $
             "abstract type variable "++show r++" cannot escape in type "++
             show ty ++" of "++show(MPr b) )
     return ty
   where
   eitherVar = either (Left . Var) (Right . Var)
ti kctx ictx ctx (Lam b) =
  do (x, t) <- unbind b
     ty1 <- Var <$> fresh "_"
     ty2 <- ti kctx ictx ((x, bind [] ty1) : ctx) t
     return (TArr ty1 ty2)
ti kctx ictx ctx (App t1 t2) =
  do ty1 <- ti kctx ictx ctx t1
     ty2 <- ti kctx ictx ctx t2
     ty <- Var <$> fresh "a"
     lift $ unify (TArr ty2 ty) ty1
     return ty
ti kctx ictx ctx (Let b) =
  do ((x, Embed t1), t2) <- unbind b
     ty <- ti kctx ictx ctx t1
     u <- getSubst
     tysch <- closeTy kctx ctx (foldr (.) id (map (uncurry subst) u) ty)
     ti kctx ictx ((x, tysch) : ctx) t2
ti kctx ictx ctx (Alt _ []) = throwError(strMsg "empty Alts")
ti kctx ictx ctx (Alt Nothing as) = -- TODO coverage of all ctors
  do tys <- mapM (tiAlt kctx ictx ctx) as
     lift $ unifyMany (zip tys (tail tys))
     return (head tys)
ti kctx ictx ctx (Alt (Just im) as) = -- TODO coverage of all ctors
  do tys <- mapM (tiAlt kctx ictx ctx) as
     u <- getSubst
     let (Right tcon : args) =
            tApp2list $ case (head tys) of
                          TArr t _ -> foldr (.) id (map (uncurry subst) u) t
     (is, rngty) <- unbind im
     when (1 + length is > length args)
        $ throwError(strMsg $ "too many indices in "++show im)
     let args' = replaceSuffix args (map eitherVar is)
     let domty = foldl TApp tcon args'
     let tysch = bind is (TArr domty rngty)
     tys' <- mapM freshInst (replicate (length as) tysch)
     lift $ unifyMany (zip tys' tys)
     return =<< freshInst tysch
   where
   eitherVar = either (Left . Var) (Right . Var)

replaceSuffix xs ys = reverse (drop (length ys) (reverse xs)) ++ ys

tApp2list (TApp ty1 targ) = tApp2list ty1 ++ [targ]
tApp2list ty             = [Right ty]

app2list (App t1 t2) = app2list t1 ++ [t2]
app2list t           = [t]



tiAlt kctx ictx ctx (x,b) =
  do xTy <- case lookup x ictx of
                 Nothing -> throwError . strMsg $ show x ++ " undefined"
                 Just xt -> freshInst xt
     u <- getSubst
     let xty = foldr (.) id (map (uncurry subst) u) xTy
     let xtyUnfold = unfoldTArr xty
     let (xtyArgs, xtyRet) = (init xtyUnfold, last xtyUnfold)
     let xTyVars = nub $ (fv xty \\ fvTmInTy xty)
                      \\ (fv kctx ++ fv ictx ++ fv ctx)
     let xTmVars = nub $ (fvTmInTy xty \\ fv xtyRet)
                      \\ (fv kctx ++ fv ictx ++ fv ctx)
     let eTyVars = xTyVars \\ fv xtyRet
     let eTmVars = xTmVars \\ fv xtyRet
     -- substitute existential vars as bogus TCon or Con to avoid unification
     let xty' = foldr (.) id (  [LN.subst nm (TCon nm) | nm <- eTyVars] 
                             ++ [LN.subst nm (Con nm)  | nm <- eTmVars] ) xty
     let xtyArgs' = init (unfoldTArr xty')
     let kctx' = kctx
     let ictx' = ictx
     -- -- adding existental TCon or Con to context seems unnecessary
     -- kctx' <- (++) <$> sequence [(,) nm <$> (Var <$> fresh "k") | nm <- eTyVars]
     --               <*> return kctx
     -- ictx' <- (++) <$> sequence [(,) nm <$> (bind [] . Var <$> fresh "c")
     --                             | nm <- eTmVars]
     --               <*> return ictx
     (ns,t) <- unbind b
     let ctx' = zip ns (map (bind []) xtyArgs') ++ ctx
     -- -- code before considering existentials
     -- tyvars <- sequence $ replicate (length ns) (bind [] <$> Var <$> fresh "a")
     -- let ctx' = zip ns tyvars ++ ctx
     domty <- ti kctx' ictx' ctx' (foldl1 App (Con x : map Var ns))
     rngty <- ti kctx' ictx' ctx' t
     lift $ unify xtyRet domty
     u <- getSubst
     let ty = foldr (.) id (map (uncurry subst) u) (TArr domty rngty)
     let TArr domty rngty = ty
     let eRetVars = intersect (eTyVars ++ eTmVars) (fv ty)
     unless (trace (show ty) $ null eRetVars) (throwError . strMsg $
                              "rigid variables "++ show eRetVars ++
                              " in the return type "++ show rngty ++
                              " of "++ show t)
     return $ trace
                ("return type: "++show ty ++ "\n"++
                 show(eTyVars::[TyName]
                     ,fv xtyRet::[TyName]
                     ,eTyVars\\fv xtyRet::[TyName])
                 ++
                 "\n\t"++ show eTyVars++" of "++show xtyRet ++ show(fv xtyRet::[TyName])++" in "++show (x,b))
              ty

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

ti' ctx = runTI . ti [] [] ctx

ty = runTI $ ti [] [] [] (lam _x x)


unbindTySch tsch = snd (unsafeUnbind tsch)


-- evaluation

sreturn ctx t = return $ foldr (.) id (map (uncurry LN.subst) ctx) t

ev ctx (Var x) =
  case lookup x ctx of
    Nothing -> throwError(strMsg $ name2String x++" undefined")
    Just v  -> return v
ev ctx v@(Con x) = return v
ev ctx (In n t) = In n <$> ev ctx t
ev ctx v@(MIt b) = return v
ev ctx v@(MPr b) = return v
ev ctx v@(Lam b) = return v
ev ctx (App t1 t2) =
  do v1 <- ev ctx t1
     v2 <- ev ctx t2
     case v1 of
       Var x -> error $ show x ++ " (free variable): should never happen"
       Con _ -> return $ App v1 v2
       In _ _ -> return $ App v1 v2
       App _ _ -> return $ App v1 v2
       Lam b -> do (x, t) <- unbind b
                   let ctx' = (x,v2) : ctx
                   sreturn [(x,v2)] =<< ev ctx' t
       MIt b -> do (f,t) <- unbind b
                   let ctx' = (f,v1) : ctx
                   let In _ v = v2
                   sreturn [(f,v1)] =<< ev ctx' (App t v)
       MPr b -> do ((f,cast),t) <- unbind b
                   let ctx' = (f,v1) : (cast,lam _x x) : ctx
                   let In _ v = v2
                   sreturn [(f,v1),(cast,lam _x x)] =<< ev ctx' (App t v)
       Alt m as ->
         do let (Con c:vs) = app2list v2
            case lookup c as of
              Nothing -> throwError(strMsg $ name2String c++" undefined")
              Just b  ->
                do (xs,t) <- unbind b
                   let ctx' = zip xs vs ++ ctx
                   sreturn (zip xs vs) =<< ev ctx' t
ev ctx (Let b) = do ((x, Embed t1), t2) <- unbind b
                    v1 <- ev ctx t1
                    let ctx' = (x,v1) : ctx
                    sreturn [(x,v1)] =<< ev ctx' t2
ev ctx v@(Alt _ _) = return v



norm ctx v@(Var x) =
  case lookup x ctx of
    Nothing -> return v
    Just v  -> return v
norm ctx v@(Con x) = return v
norm ctx (In n t) = In n <$> norm ctx t
norm ctx (MIt b) = do (xs,t) <- unbind b
                      MIt <$> (bind xs <$> norm ctx t)
norm ctx (MPr b) = do (xs,t) <- unbind b
                      MPr <$> (bind xs <$> norm ctx t)
norm ctx (Lam b) = do (x, t) <- unbind b
                      Lam . bind x <$> norm ctx t
norm ctx (App t1 t2) =
  do v1 <- norm ctx t1
     v2 <- norm ctx t2
     case v1 of
       Var x -> return $ App v1 v2
       Con _ -> return $ App v1 v2
       In _ _ -> return $ App v1 v2
       App _ _ -> return $ App v1 v2
       Lam b -> do (x, t) <- unbind b
                   let ctx' = (x,v2) : ctx
                   sreturn [(x,v2)] =<< norm ctx' t
       MIt b -> do (f,t) <- unbind b
                   let ctx' = (f,v1) : ctx
                   let In _ v = v2
                   sreturn [(f,v1)] =<< norm ctx' (App t v)
       MPr b -> do ((f,cast),t) <- unbind b
                   let ctx' = (f,v1) : (cast,lam _x x) : ctx
                   let In _ v = v2
                   sreturn [(f,v1),(cast,lam _x x)] =<< norm ctx' (App t v)
       Alt m as ->
         do let (Con c:vs) = app2list v2
            case lookup c as of
              Nothing -> throwError(strMsg $ name2String c++" undefined")
              Just b  ->
                do (xs,t) <- unbind b
                   let ctx' = zip xs vs ++ ctx
                   sreturn (zip xs vs) =<< norm ctx' t
norm ctx (Let b) = do ((x, Embed t1), t2) <- unbind b
                      v1 <- norm ctx t1
                      let ctx' = (x,v1) : ctx
                      sreturn [(x,v1)] =<< norm ctx' t2
norm ctx (Alt m as) =
  Alt m <$> sequence [ do (xs,t) <- unbind b
                          (,) c <$> (bind xs <$> norm ctx t)
                      | (c,b) <- as ]
