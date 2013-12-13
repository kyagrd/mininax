{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
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
-- import Generics.RepLib
import Generics.RepLib.Unify
import Unbound.LocallyNameless hiding (subst, Con)
import GHC.Exts( IsString(..) )

import Syntax

instance HasVar TyName Ty where
  is_var (TVar nm) = Just nm
  is_var _ = Nothing
  var = TVar

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
  where errstr = "cannot unify "++printTy t1++" and "++printTy t2

mguMany ps =
  case solveUnification ps of
    Nothing -> throwError (strMsg errstr)
    Just u -> return u
  where errstr = "cannot unify "++show ps


getSubst = do { UState _ s <- lift get; return s }

extSubst = mapM_ extendSubstitution

-- unify :: Ty -> Ty -> UM TyName Ty ()
unify t1 t2 =
  do s <- getSubst
     u <- mgu (uapply s t1) (uapply s t2)
     extSubst u

unifyMany ps =
  do s <- getSubst
     u <- mguMany [(uapply s t1, uapply s t2) | (t1, t2) <- ps]
     extSubst u


type Ctx = [(TmName,TySch)]

type TySch = Bind [TyName] Ty

-- freshInst :: Fresh m => TySch -> m Ty
freshInst tysch = liftM snd (unbind tysch)
closeTy :: Ctx -> Ty -> TySch
closeTy ctx ty = bind (fv ty \\ fv ctx) ty

type TI = FreshMT (ErrorT UnifyError (State (UnificationState TyName Ty)))

-- TODO catch errors and append more context info
ti :: Ctx -> Tm -> TI Ty
ti ctx (Var x)  = case lookup x ctx of
                    Nothing -> throwError(strMsg $ name2String x++" undefined")
                    Just ty -> freshInst ty
ti ctx (Con x)  = case lookup x ctx of
                    Nothing -> throwError(strMsg $ name2String x++" undefined")
                    Just ty -> freshInst ty
ti ctx (Lam b)  = do (x, t) <- unbind b
                     ty1 <- TVar <$> fresh "a"
                     ty2 <- ti ((x, bind [] ty1) : ctx) t
                     return (TArr ty1 ty2)
ti ctx (App t1 t2) =
                  do ty1 <- ti ctx t1
                     ty2 <- ti ctx t2
                     ty <- TVar <$> fresh "a"
                     lift $ unify (TArr ty2 ty) ty1
                     return ty
ti ctx (Let b)  = do ((x, Embed t1), t2) <- unbind b
                     ty <- ti ctx t1
                     let tysch = closeTy ctx ty
                     ti ((x, tysch) : ctx) t2
ti ctx (Alt _ []) = throwError(strMsg "empty Alts")
ti ctx (Alt Nothing as) =
                  do tys <- mapM (tiAlt ctx) as
                     lift $ unifyMany (zip tys (tail tys))
                     return (head tys)
ti ctx (Alt (Just im) as) =
                  do tys <- mapM (tiAlt ctx) as
                     let (tcon : args) = tApp2list (head tys) 
                     (is, rngty) <- unbind im
                     when (length is > length args)
                        $ throwError(strMsg $ "too many indices in "++show im)
                     let args' = replaceSuffix args (map TVar is)
                     let domty = foldl1 TApp (tcon : args')
                     let tysch = bind is (TArr domty rngty)
                     tys' <- mapM freshInst (replicate (length as) tysch)
                     lift $ unifyMany (zip tys' tys)
                     freshInst tysch


replaceSuffix xs ys = reverse (drop (length ys) (reverse xs)) ++ ys

tApp2list (TApp ty1 ty2) = tApp2list ty1 ++ [ty2]
tApp2list ty             = [ty]

-- not considering existentials or generic existentials yet
tiAlt ctx (x,b) =
  do (ns,t) <- unbind b -- (Con x) applied to (map Var ns) -> t
     domty <- ti ctx (Con x)
     let (tcon : args) = tApp2list domty
     rngty <- ti (zip ns (map (bind []) args) ++ ctx) t
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

ti' ctx = runTI . ti ctx

ty = runTI $ ti [] (lam _x x)

-- start writing tyinfer as if there were only * kinded TyVar
