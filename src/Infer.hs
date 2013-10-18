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
                  do tys <- mapM tiAlt as
                     lift $ unifyMany (zip tys (tail tys))
                     return (head tys)
ti ctx (Alt (Just im) as) = error "ti ctx (Alt as)"
--                  do error "ti ctx (Alt as)"
--                     error "ti ctx (Alt as)"


tiAlt = undefined

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

{-

*Infer> :browse Generics.RepLib.Unify
class HasVar a b where
  is_var :: b -> Maybe a
  var :: a -> b
class Occurs n a b where
  occursCheck :: n -> Proxy a -> b -> Bool
data Proxy a
class Generics.RepLib.Unify.Subst a t t' where
  Generics.RepLib.Unify.subst :: a -> t -> t' -> t'
data UConstraint n a where
  UC :: (UnifySubD n a b) -> b -> b -> UConstraint n a
type UM n a b =
  ErrorT
    UnifyError
    (Control.Monad.Trans.State.Lazy.State (UnificationState n a))
    b
data UnificationState n a
  = UState {uConstraints :: [UConstraint n a], uSubst :: [(n, a)]}
class (Eq n, Show n, Show a, Show b,
       HasVar n a) => Unify n a b where
  unifyStep :: Proxy (n, a) -> b -> b -> UM n a ()
type UnifyError = String
data UnifySubD n a b
  = UnifySubD {unifyStepD :: Proxy (n, a) -> b -> b -> UM n a (),
               substD :: n -> a -> b -> b,
               occursCheckD :: n -> Proxy a -> b -> Bool}
addConstraintsRL1 ::
  MTup (UnifySubD n a) l -> Proxy (n, a) -> l -> l -> UM n a ()
dequeueConstraint :: UM n a (Maybe (UConstraint n a))
extendSubstitution ::
  (HasVar n a, Eq n, Show n, Show a, Rep1 (UnifySubD n a) a) =>
  (n, a) -> UM n a ()
occursCheckR1 ::
  Rep1 (UnifySubD n a) b =>
  R1 (UnifySubD n a) b -> n -> Proxy a -> b -> Bool
queueConstraint :: UConstraint n a -> UM n a ()
solveUnification ::
  (HasVar n a, Eq n, Show n, Show a, Rep1 (UnifySubD n a) a) =>
  [(a, a)] -> Maybe [(n, a)]
solveUnification' ::
  (HasVar n a, Eq n, Show n, Show a, Show b,
   Rep1 (UnifySubD n a) b) =>
  Proxy (n, a) -> [(b, b)] -> Maybe [(n, a)]
substR1 ::
  Rep1 (UnifySubD a t) t' =>
  R1 (UnifySubD a t) t' -> a -> t -> t' -> t'
unifyStepEq :: (Eq b, Show b) => b -> b -> UM n a ()
unifyStepR1 ::
  (Eq n, Show n, Show a, Show b, HasVar n a) =>
  R1 (UnifySubD n a) b -> Proxy (n, a) -> b -> b -> UM n a ()

 -}

-- start writing tyinfer as if there were only * kinded TyVar
