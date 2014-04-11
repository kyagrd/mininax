-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE NoMonomorphismRestriction,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             OverloadedStrings
    #-}
-----------------------------------------------------------------------------
--
-- Module      :  InferDec
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

module InferDec where

import Data.List
import Control.Monad
import Control.Monad.Trans
import Control.Applicative
import Unbound.LocallyNameless ( fresh, string2Name )
import GHC.Exts( IsString(..) )

import Syntax
import Parser ( Dec(..), LIdent(..), UIdent(..), DataAlt(..) )
import Parser ( type2Ty, term2Tm )
-- import qualified Parser as P
import Infer

tiDecs kctx ds = foldl1 (>=>) (map (tiDec kctx) ds)

tiDec :: KCtx -> Dec -> Ctx -> TI Ctx
tiDec kctx (Def (LIdent x) t) ctx =
  do ty <- ti kctx ctx (term2Tm t)
     u <- getSubst
     return $ (string2Name x, closeTy kctx ctx (uapply u ty)) : ctx
tiDec kctx (Data (UIdent tc) is dAlts) ctx =
  do return $ [ (string2Name c, closeTy kctx ctx (foldr TArr retTy $ map type2Ty ts))
               | DAlt (UIdent c) ts <- dAlts ] ++ ctx
  where retTy = foldl1 TApp ( TCon(string2Name tc) : 
                              [TVar(string2Name a) | LIdent a <- is] )

kiData :: Dec -> KCtx -> KI KCtx
kiData (Data (UIdent tc) is dAlts) kctx =
  do ctx <- sequence [ (,) (string2Name a :: TyName)
                       <$> (KVar <$> fresh "k")    | LIdent a <- is ]
     mapM (kiDAlt $ ctx ++ kctx) dAlts
     return $ (string2Name tc, foldr KArr Star (map snd ctx)) : kctx
kiData _ _ = error "not a data declaration"

kiDataDecs ds = foldl1 (>=>) (map kiData ds)

kiDAlt :: KCtx -> DataAlt -> KI ()
kiDAlt ctx (DAlt _ ts) =
  do ks <- mapM (ki ctx) (map type2Ty ts)
     lift $ unifyMany (zip (repeat Star) ks)


