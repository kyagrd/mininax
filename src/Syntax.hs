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

module Syntax ( PSUT(..)
 , TmName, Tm, isTm -- (..)
 , TyName, Ty, isTy -- (..)
 , KiName, Ki, isKi -- (..)
 , KArg, TArg, TArgName
) where

import Unbound.LocallyNameless hiding (Con)
import GHC.Exts( IsString(..) )

type KiName = Name Ki
type TyName = Name Ty
type TmName = Name Tm

data PSUT
  -- data Ki
        -- = KVar KiName
        = Star
        | KArr KArg Ki 
  -- data Ty
        -- = TVar TyName -- argument must be (V nm)
        | TCon TyName
        | TArr Ty Ty
        | TApp Ty TArg
        | TFix Ty -- Ty must be TCon or application of TCon to other arguments
  -- data Tm
        | Var TmName -- argument must be (V nm)
        | Con TmName
        | In Integer Tm
        | MIt (Bind TmName Tm) -- Tm must be Alt
        | MPr (Bind (TmName,TmName) Tm) -- Tm must be Alt
        | Lam (Bind TmName Tm)
        | App Tm Tm
        | Let (Bind (TmName, Embed Tm) Tm)
        | Alt (Maybe IxMap) [(TmName,(Bind [TmName] Tm))]

type Ki = PSUT
type Ty = PSUT
type Tm = PSUT

isKi (Var _)   = True
isKi Star       = True
isKi (KArr _ _) = True
isKi _          = False

isTy (Var _)   = True
isTy (TCon _)   = True
isTy (TArr _ _) = True
isTy (TApp _ _) = True
isTy (TFix _)   = True
isTy _          = False

isTm (Var _)    = True
isTm (Con _)    = True
isTm (In _ _)   = True
isTm (MIt _)    = True
isTm (MPr _)    = True
isTm (Lam _)    = True
isTm (App _ _)  = True
isTm (Let _)    = True
isTm (Alt _ _)  = True
isTm _          = False

type KArg = Either Ty Ki -- RIght is Ki, Left is Ty
type TArg = Either Tm Ty -- Right is Ty, Left is Tm

-- assuming only variable form of indicies in IxMap
type IxMap = Bind [TArgName] Ty

type TArgName = Either TmName TyName -- Right is TyName, Left is TmName

-- $(derive [''Ki, ''Ty, ''Tm])
$(derive [''PSUT])

-- names as string literals
instance Rep a => IsString (Name a) where
  fromString = string2Name


-- Alpha and Sbust instances are in Parser module
-- in order to avoid mutually recursive module imports
-- since Show class instantces for Ki, Ty, Tm depends on LBNF functions

