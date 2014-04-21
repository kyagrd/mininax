-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             OverloadedStrings,
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
   TmName, Tm(..) -- , printTm
 , TyName, Ty(..) -- , printTy
 , KiName, Ki(..) -- , printKi
) where

import Unbound.LocallyNameless hiding (Con)
import Unbound.LocallyNameless.Ops (unsafeUnbind)
-- import qualified Data.Set as S
import Data.List (intersperse)
import GHC.Exts( IsString(..) )
-- import Language.LBNF (printTree)
-- import {-# SOURCE #-} Parser (ki2Kind, ty2Type, tm2Term)

type KiName = Name Ki
type TyName = Name Ty
type TmName = Name Tm

data Ki = KVar KiName
        | Star
        | KArr Ki Ki
   -- deriving Show

data Ty = TVar TyName
        | TCon TyName
        | TArr Ty Ty
        | TApp Ty Ty
        | TFix Ty -- Ty must be TCon or application of TCon to other arguments
   -- deriving Show

data Tm = Var TmName
        | Con TmName
        | In Integer Tm
        | MIt (Bind TmName Tm) -- Tm must be Alt
        | MPr (Bind (TmName,TmName) Tm) -- Tm must be Alt
        | Lam (Bind TmName Tm)
        | App Tm Tm
        | Let (Bind (TmName, Embed Tm) Tm)
        | Alt (Maybe IxMap) [(TmName,(Bind [TmName] Tm))]
   -- deriving Show

-- assuming only variable form of indicies in IxMap
type IxMap = Bind [TyName] Ty

$(derive [''Ki, ''Ty, ''Tm])

-- names as string literals
instance Rep a => IsString (Name a) where
  fromString = string2Name


-- Alpha and Sbust instances are in Parser module
-- in order to avoid mutually recursive module imports
-- since Show class instantces for Ki, Ty, Tm depends on LBNF functions

