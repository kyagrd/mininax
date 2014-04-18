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

