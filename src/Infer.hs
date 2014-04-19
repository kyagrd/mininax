-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE TemplateHaskell,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             OverloadedStrings,
             GADTs,
             NoMonomorphismRestriction,
             CPP #-}

module Infer where

-- import Data.Char
import Data.List
import Control.Applicative
-- import Control.Monad
import Control.Monad.Trans
import Control.Monad.Error
import Control.Monad.State
import Language.LBNF.Runtime
import Parser ()
-- import Generics.RepLib
import Generics.RepLib.Unify
import Unbound.LocallyNameless hiding (subst, Con)
import qualified Unbound.LocallyNameless as LN
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import GHC.Exts( IsString(..) )

import Syntax

instance HasVar KiName Ki where
  is_var (KVar nm) = Just nm
  is_var _ = Nothing
  var = KVar

instance HasVar TyName Ty where
  is_var (TVar nm) = Just nm
  is_var _ = Nothing
  var = TVar

-- do not break down names for unification
instance (Eq n, Show n, HasVar n Ki) => Unify n Ki (Name s) where
   unifyStep _ = unifyStepEq

-- do not break down strings for unification
instance (Eq n, Show n, HasVar n Ki) => Unify n Ki String where
  unifyStep _ = unifyStepEq

-- do not break down names for unification
instance (Eq n, Show n, HasVar n Ty) => Unify n Ty (Name s) where
  unifyStep _ = unifyStepEq

-- do not break down strings for unification
instance (Eq n, Show n, HasVar n Ty) => Unify n Ty String where
  unifyStep _ = unifyStepEq

uapply s = foldr (.) id (map (uncurry subst) s)

mgu t1 t2 =
  case solveUnification [(t1, t2)] of
    Nothing -> throwError (strMsg errstr)
    Just u -> return u
  where errstr = "cannot unify "++printTree t1++" and "++printTree t2

mguMany ps =
  case solveUnification ps of
    Nothing -> throwError (strMsg errstr)
    Just u -> return u
  where errstr = "cannot unify \n" ++
                 ( concat [ "\t"++printTree t1++" and "++printTree t2++"\n"
                          | (t1,t2)<-ps ] )


getSubst = do { UState _ s <- lift get; return s }

extSubst = mapM_ extendSubst


extendSubst (x,t) =
  do u <- getSubst
     case lookup x u of
       Nothing -> extendSubstitution (x,t)
       Just t' -> unify t t' >> extendSubstitution (x,t)


-- unify :: Ty -> Ty -> UM TyName Ty ()
unify t1 t2 =
  do s <- getSubst
     u <- mgu (uapply s t1) (uapply s t2)
     extSubst u

unifyMany ps =
  do s <- getSubst
     u <- mguMany [(uapply s t1, uapply s t2) | (t1, t2) <- ps]
     extSubst u


type KCtx = [(TyName,Ki)]
type KI = FreshMT (ErrorT UnifyError (State (UnificationState KiName Ki)))


ki :: KCtx -> Ty -> KI Ki
ki ctx (TVar x)  = case lookup x ctx of
                     Nothing -> throwError(strMsg $ name2String x++" undefined")
                     Just k -> return k -- currently just simple kinds
ki ctx (TCon x)  = case lookup x ctx of
                     Nothing -> throwError(strMsg $ name2String x++" undefined")
                     Just k -> return k -- currently just simple kinds
ki ctx (TArr t1 t2) =
                  do k1 <- ki ctx t1
                     k2 <- ki ctx t2
                     lift $ unify Star k1
                     lift $ unify Star k2
                     return Star
ki ctx (TApp t1 t2) =
                  do k1 <- ki ctx t1
                     k2 <- ki ctx t2
                     k <- KVar <$> fresh "k"
                     lift $ unify (KArr k2 k) k1
                     return k

ki ctx (TFix t) = do k1 <- ki ctx t
                     k <- KVar <$> fresh "k"
                     lift $ unify (KArr k k) k1
                     return k


-- freshInst :: Fresh m => TySch -> m Ty
freshInst tysch = liftM snd (unbind tysch)
-- closeTy :: Ctx -> Ty -> TySch
-- closeTy ctx ty = bind (nub(fv ty \\ fv ctx)) ty

closeTy :: KCtx -> Ctx -> Ty -> TySch
closeTy kctx ctx ty = bind (nub((fv ty \\ fv ctx) \\ fv kctx)) ty



type Ctx = [(TmName,TySch)]
type TI = FreshMT (ErrorT UnifyError (State (UnificationState TyName Ty)))

type TySch = Bind [TyName] Ty


kargs = unfoldr (\k -> case k of { KArr k1 k2 -> Just(k1,k2) ; _ -> Nothing })

arity nm kctx = length (kargs k)
   where Just k = lookup nm kctx

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

-- TODO catch errors and append more context info
ti :: KCtx -> Ctx -> Tm -> TI Ty
ti kctx ctx (Var x) =
  case lookup x ctx of
    Nothing -> throwError(strMsg $ name2String x++" undefined")
    Just tysch -> return =<< freshInst tysch
ti kctx ctx (Con x) =
  case lookup x ctx of
    Nothing -> throwError(strMsg $ name2String x++" undefined")
    Just tysch -> return =<< freshInst tysch
ti kctx ctx (In n t) -- this is a hacky implementation without checking kinds
  | n < 0     = error "In[n] should have non-negative n"
  | otherwise = do ty <- ti kctx ctx t
                   let m = fromInteger n
                   is <- sequence $ replicate m (TVar <$> fresh "i")
                   ty1 <- TVar <$> fresh "t"
                   lift $ unify (foldl TApp ty1 (TFix ty1 : is)) ty
                   return $ foldl TApp (TFix ty1) is
ti kctx ctx (MIt b) =
  do (f,tm@(Alt mphi as)) <- unbind b
     r <- fresh "r"
     t <- fresh "t"
     (is, tyret) <- case mphi of Nothing  -> (,) [] <$> (TVar <$> fresh "b")
                                 Just phi -> unbind phi
     let tyf = foldl1 TApp (TCon r : map TVar is) `TArr` tyret
     let tytm = foldl1 TApp (TVar t : TCon r : map TVar is) `TArr` tyret
     let kctx' = (r, undefined {- TODO this is hack -}) : kctx
     let ctx' = (f,bind is tyf) : ctx
     tytm' <- ti kctx' ctx' tm
     lift $ unify tytm tytm'
     return $ foldl TApp (TFix(TVar t)) (map TVar is) `TArr` tyret
ti kctx ctx (Lam b) =
  do (x, t) <- unbind b
     ty1 <- TVar <$> fresh "a"
     ty2 <- ti kctx ((x, bind [] ty1) : ctx) t
     return (TArr ty1 ty2)
ti kctx ctx (App t1 t2) =
  do ty1 <- ti kctx ctx t1
     ty2 <- ti kctx ctx t2
     ty <- TVar <$> fresh "a"
     lift $ unify (TArr ty2 ty) ty1
     return ty
ti kctx ctx (Let b) =
  do ((x, Embed t1), t2) <- unbind b
     ty <- ti kctx ctx t1
     let tysch = closeTy [] ctx ty
     ti kctx ((x, tysch) : ctx) t2
ti kctx ctx (Alt _ []) = throwError(strMsg "empty Alts")
ti kctx ctx (Alt Nothing as) =
  do tys <- mapM (tiAlt kctx ctx) as
     lift $ unifyMany (zip tys (tail tys))
     return (head tys)
ti kctx ctx (Alt (Just im) as) =
  do tys <- mapM (tiAlt kctx ctx) as
     let (tcon : args) = tApp2list $ case (head tys) of TArr t _ -> t
     (is, rngty) <- unbind im
     when (length is > length args)
        $ throwError(strMsg $ "too many indices in "++show im)
     let args' = replaceSuffix args (map TVar is)
     let domty = foldl1 TApp (tcon : args')
     let tysch = bind is (TArr domty rngty)
     tys' <- mapM freshInst (replicate (length as) tysch)
     lift $ unifyMany (zip tys' tys)
     return =<< freshInst tysch


replaceSuffix xs ys = reverse (drop (length ys) (reverse xs)) ++ ys

tApp2list (TApp ty1 ty2) = tApp2list ty1 ++ [ty2]
tApp2list ty             = [ty]

app2list (App t1 t2) = app2list t1 ++ [t2]
app2list t           = [t]



-- not considering existentials or generic existentials yet
tiAlt kctx ctx (x,b) =
  do (ns,t) <- unbind b
     tyvars <- sequence $ replicate (length ns) (bind [] <$> TVar <$> fresh "a")
     let ctx' = zip ns tyvars ++ ctx
     domty <- ti kctx ctx' (foldl1 App (Con x : map Var ns))
     rngty <- ti kctx ctx' t
     return (TArr domty rngty)

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

ti' ctx = runTI . ti [] ctx

ty = runTI $ ti [] [] (lam _x x)


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
ev ctx v@(Lam b) = return v
ev ctx (App t1 t2) =
  do v1 <- ev ctx t1
     v2 <- ev ctx t2
     case v1 of
       Var x -> error $ show x ++ " should never happen" -- return $ App v1 v2 -- should never happen
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



