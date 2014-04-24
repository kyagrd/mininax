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
   TmName, Tm(..)
 , TyName, Ty(..)
 , KiName, Ki(..)
) where

import Unbound.LocallyNameless hiding (Con)
import GHC.Exts( IsString(..) )

type KiName = Name Ki
type TyName = Name Ty
type TmName = Name Tm

data Ki = KVar KiName
        | Star
        | KArr KArg Ki 
   -- deriving Show

type KArg = Either Ty Ki

data Ty = TVar TyName
        | TCon TyName
        | TArr Ty Ty
        | TApp Ty TArg
        | TFix Ty -- Ty must be TCon or application of TCon to other arguments
   -- deriving Show

type TArg = Either Tm Ty

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
type IxMap = Bind [TArgName] Ty

type TArgName = Either TmName TyName

$(derive [''Ki, ''Ty, ''Tm])

-- names as string literals
instance Rep a => IsString (Name a) where
  fromString = string2Name


-- Alpha and Sbust instances are in Parser module
-- in order to avoid mutually recursive module imports
-- since Show class instantces for Ki, Ty, Tm depends on LBNF functions

