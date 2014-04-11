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

import Data.Char
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
                     Just k -> ureturn k -- currently just simple kinds
ki ctx (TCon x)  = case lookup x ctx of
                     Nothing -> throwError(strMsg $ name2String x++" undefined")
                     Just k -> ureturn k -- currently just simple kinds
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
                     ureturn k

ki ctx (TFix t) = do k1 <- ki ctx t
                     k <- KVar <$> fresh "k"
                     lift $ unify (KArr k k) k1
                     ureturn k


-- freshInst :: Fresh m => TySch -> m Ty
freshInst tysch = liftM snd (unbind tysch)
-- closeTy :: Ctx -> Ty -> TySch
-- closeTy ctx ty = bind (nub(fv ty \\ fv ctx)) ty

closeTy :: KCtx -> Ctx -> Ty -> TySch
closeTy kctx ctx ty = bind (nub((fv ty \\ fv ctx) \\ fv kctx)) ty



type Ctx = [(TmName,TySch)]
type TI = FreshMT (ErrorT UnifyError (State (UnificationState TyName Ty)))

type TySch = Bind [TyName] Ty


ureturn ty = do { u <- getSubst; return (uapply u ty) }

-- TODO catch errors and append more context info
ti :: KCtx -> Ctx -> Tm -> TI Ty
ti kctx ctx (Var x) =
  case lookup x ctx of
    Nothing -> throwError(strMsg $ name2String x++" undefined")
    Just tysch -> ureturn =<< freshInst tysch
ti kctx ctx (Con x) =
  case lookup x ctx of
    Nothing -> throwError(strMsg $ name2String x++" undefined")
    Just tysch -> ureturn =<< freshInst tysch
ti kctx ctx (In n t)
  | n < 0     = error "In[n] should have non-negative n"
  | otherwise = do ty <- ti kctx ctx t
                   let m = fromInteger n
                   is <- sequence $ replicate m (TVar <$> fresh "i")
                   ty1 <- TVar <$> fresh "t"
                   lift $ unify (foldl TApp ty1 (TFix ty1 : is)) ty
                   ureturn $ foldl TApp (TFix ty1) is
ti kctx ctx (Lam b) =
  do (x, t) <- unbind b
     ty1 <- TVar <$> fresh "a"
     ty2 <- ti kctx ((x, bind [] ty1) : ctx) t
     ureturn (TArr ty1 ty2)
ti kctx ctx (App t1 t2) =
  do ty1 <- ti kctx ctx t1
     ty2 <- ti kctx ctx t2
     ty <- TVar <$> fresh "a"
     lift $ unify (TArr ty2 ty) ty1
     ureturn ty
ti kctx ctx (Let b) =
  do ((x, Embed t1), t2) <- unbind b
     ty <- ti kctx ctx t1
     let tysch = closeTy [] ctx ty
     ti kctx ((x, tysch) : ctx) t2
ti kctx ctx (Alt _ []) = throwError(strMsg "empty Alts")
ti kctx ctx (Alt Nothing as) =
  do tys <- mapM (tiAlt kctx ctx) as
     lift $ unifyMany (zip tys (tail tys))
     ureturn (head tys)
ti kctx ctx (Alt (Just im) as) =
  do tys <- mapM (tiAlt kctx ctx) as
     let (tcon : args) = tApp2list (head tys) 
     (is, rngty) <- unbind im
     when (length is > length args)
        $ throwError(strMsg $ "too many indices in "++show im)
     let args' = replaceSuffix args (map TVar is)
     let domty = foldl1 TApp (tcon : args')
     let tysch = bind is (TArr domty rngty)
     tys' <- mapM freshInst (replicate (length as) tysch)
     lift $ unifyMany (zip tys' tys)
     ureturn =<< freshInst tysch


replaceSuffix xs ys = reverse (drop (length ys) (reverse xs)) ++ ys

tApp2list (TApp ty1 ty2) = tApp2list ty1 ++ [ty2]
tApp2list ty             = [ty]

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

-- start writing tyinfer as if there were only * kinded TyVar
