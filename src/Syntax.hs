-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             OverloadedStrings,
             GADTs,
             CPP #-}
-----------------------------------------------------------------------------
--
-- Module      :  Syntax
-- Copyright   :  BSD
-- License     :  AllRightsReserved
--
-- Maintainer  :  Ki Yung Ahn
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Syntax (
   TmName, Tm(..), printTm
 , TyName, Ty(..), printTy
 , KiName, Ki(..), printKi
 , name2str
) where

-- import Control.Monad
-- import Control.Monad.Trans.Error

import Unbound.LocallyNameless hiding (Con)
import Unbound.LocallyNameless.Ops (unsafeUnbind)
-- import qualified Data.Set as S
import Data.List (intersperse)
import GHC.Exts( IsString(..) )

type KiName = Name Ki
type TyName = Name Ty
type TmName = Name Tm

data Ki = KVar KiName
        | Star
        | KArr Ki Ki
   deriving Show

data Ty = TVar TyName
        | TCon TyName
        | TArr Ty Ty
        | TApp Ty Ty
        | TFix Ty -- Ty must be TCon or application of TCon to other arguments
   deriving Show

data Tm = Var TmName
        | Con TmName
        | In Integer Tm
        | MIt (Bind TmName Tm) -- Tm must be Alt
        | Lam (Bind TmName Tm)
        | App Tm Tm
        | Let (Bind (TmName, Embed Tm) Tm)
        | Alt (Maybe IxMap) [(TmName,(Bind [TmName] Tm))]
   deriving Show

-- assuming only variable form of indicies in IxMap
type IxMap = Bind [TyName] Ty

$(derive [''Ki, ''Ty, ''Tm])

------------------------------------------------------
instance Alpha Ki where
instance Alpha Ty where
instance Alpha Tm where

instance Subst Ki Ki where
  isvar (KVar x) = Just (SubstName x)
  isvar _ = Nothing
instance Subst Ty Ki where
instance Subst Ty Tm where
instance Subst Tm Ki where
instance Subst Tm Ty where
instance Subst Tm Tm where
  isvar (Var x) = Just (SubstName x)
  isvar (Con x) = Just (SubstName x)
  isvar _  = Nothing
instance Subst Ty Ty where
  isvar (TVar x) = Just (SubstName x)
  isvar (TCon x) = Just (SubstName x)
  isvar _ = Nothing

-- names as string literals
instance Rep a => IsString (Name a) where
  fromString = string2Name

-- wrapper for unless over monadic conditions

-- unlessM mb x = do b <- mb
--                   unless b x

-- simple dumb serializer using unsafeUnbind
printKi :: Ki -> String
printKi (KVar x)    = show x
printKi Star         = "*"
printKi (KArr k1 k2) = "("++printKi k1++" -> "++printKi k2++")"

printTy :: Ty -> String
printTy (TVar x) = show x
printTy (TCon x) = show x
printTy (TArr t1 t2) = "("++printTy t1++" -> "++printTy t2++")"
printTy (TApp t1 t2) = "("++printTy t1++" "++printTy t2++")"
printTy (TFix t) = "(Mu "++printTy t++")"

printTm :: Tm -> String
printTm (Var x) = show x
printTm (Con x) = show x
printTm (In n t) = "(In["++show n++"] "++printTm t++")"
printTm (MIt b) = "(MIt "++show nm ++" "++ printTm t++")"
  where (nm,t) = unsafeUnbind b
printTm (Lam b) = "(\\"++show nm++"."++printTm t++")"
  where (nm,t) = unsafeUnbind b
printTm (App t1 t2) = "("++printTm t1 ++" "++ printTm t2++")"
printTm (Let b) = "(let "++name2String nm++" = "++printTm t1++" in "++printTm t2++")"
  where ((nm,Embed t1),t2) = unsafeUnbind b
printTm (Alt mb as) = maybe "" printIxMap mb ++
  "{"++ concat (intersperse "; " (map printAlt as)) ++"}"

printAlt :: (TmName,Bind [TmName] Tm) -> [Char]
printAlt (nm,b) = unwords (map name2String (nm:nms)) ++ " -> " ++ printTm t
  where (nms,t) = unsafeUnbind b

printIxMap b = "["++ unwords (map name2String ns) ++" . "++ printTy ty ++"]"
  where (ns,ty) = unsafeUnbind b

name2str nm = name2String nm ++
              case (name2Integer nm) of { 0 -> ""; n -> show n }

{-
-----------------------------------------------------------------
-- beta-eta equivalance/reduction for types
-----------------------------------------------------------------

-- beta-eta equivalence
t1 =~ t2 | t1 `aeq` t2 = return True
t1 =~ t2 = do
    t1' <- redTy t1
    t2' <- redTy t2
    if t1' `aeq` t1 && t2' `aeq` t2
      then return False
      else t1' =~ t2'

-- Parallel beta-eta reduction, prefers beta reductions to
-- eta reductions
redTy = liftM id
{-
redTy (TVar x) = return (TVar x)
redTy (TVar x) = return (TVar x)
redTy (TArr t1 t2) = liftM2 TArr (redTy t1) (redTy t2)
redTy (TApp t1 t2) = do
  t1' <- redTy t1
  t2' <- redTy t2
  case t1' of
    -- look for a beta-reduction
    TyLam bnd -> do
        ((x,_), t1'') <- unbind bnd
        return $ subst x t2' t1''
    _ -> return $ TApp t1' t2'
redTy (TyLam bnd) = do
   ((x,ek),t) <- unbind bnd
   t' <- redTy t
   case t of
     -- look for an eta-reduction
     TApp t1 (TVar y) | y == x && x `S.notMember` fv t1 -> return t1
     _ -> return (TyLam (bind (x,ek) t'))
-}

-----------------------------------------------------------------
-- Typechecker
-----------------------------------------------------------------
type Delta = [ (TyName, Ki) ]
type Gamma = [ (TmName, Ty) ]

data Ctx = Ctx { getDelta :: Delta , getGamma :: Gamma }
emptyCtx = Ctx { getDelta = [], getGamma = [] }

type M = ErrorT String FreshM

runM :: M a -> a
runM m = case (runFreshM (runErrorT m)) of
   Left s  -> error s
   Right a -> a

checkTVar :: Ctx -> TyName -> M Ki
checkTVar g v =
    case lookup v (getDelta g) of
      Just k -> return k
      Nothing -> throwError ("NotFound "++show v)

lookupVar :: Ctx -> TmName -> M Ty
lookupVar g v =
    case lookup v (getGamma g) of
      Just s -> return s
      Nothing -> throwError ("NotFound "++show v)

extendTy :: TyName -> Ki -> Ctx -> Ctx
extendTy n k ctx = ctx { getDelta =  (n, k) : (getDelta ctx) }

extendTm :: TmName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : (getGamma ctx) }

tcty :: Ctx -> Ty -> M Ki
tcty g  (TVar x) =
   checkTVar g x
tcty g  (TCon x) =
   checkTVar g x
tcty g  (TArr t1 t2) = do
   k1 <- tcty g  t1
   unless (k1 `aeq` Star) (throwError "KindError 1")
   k2 <- tcty g  t2
   unless (k2 `aeq` Star) (throwError "KindError 2")
   return Star
tcty g  (TApp t1 t2) = do
   k1 <- tcty g t1
   k2 <- tcty g t2
   case k1 of
     KArr k11 k21 | k2 `aeq` k11 ->
       return k21
     _ -> throwError "KindError 3"

ti :: Ctx -> Tm -> M Ty
ti g (Var x) = lookupVar g x
ti g (Lam bnd) = do
  (x, t) <- unbind bnd
  unless (k1 `aeq` Star) (throwError "KindError 4")
  return (TArr ty1 ty2)
ti g (App t1 t2) = do
  ty1 <- ti g t1
  ty2 <- ti g t2
  ty1' <- redTy ty1
  case ty1' of
    TArr ty11 ty21 -> do
      unlessM (ty2 =~ ty11)
              (throwError $ "TypeError:"++__FILE__++":"++show __LINE__++":"
                          ++"expected the following types to be equal\n"
                          ++show ty2++"\n"++show ty11)
      return ty21
    _ -> throwError $ "TypeError:"++__FILE__++":"++show __LINE__++":"
                    ++"expected TArr but "++show ty1
-}
