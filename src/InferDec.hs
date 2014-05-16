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

import Syntax
import Parser ( Dec(..), LIdent(..), UIdent(..), DataAlt(..), GadtAlt(..), IVar(..) )
import Parser ( type2Ty, term2Tm, kind2Ki )
-- import qualified Parser as P
import Infer

import Data.List
import Data.Either
import Control.Monad
import Control.Monad.Error
import Control.Monad.Trans
import Control.Applicative
import Generics.RepLib.Unify (subst)
import Unbound.LocallyNameless ( bind, fresh, string2Name, aeq, fv )
import GHC.Exts( IsString(..) )
-- import Debug.Trace
trace _ a = a

-- TODO check uniqueness of TCon and Con names (not yet checking uniqueness)

tiDecs ds = foldl1 (>=>) (map tiDec ds)

tiDec :: Dec -> (KCtx,Ctx) -> TI (KCtx,Ctx)
tiDec (Def (LIdent x) t) (kctx,ictx) =
  do ty <- ti kctx ictx [] (term2Tm t)
           `catchError`
           (\e -> throwError . strMsg $ e ++ "\n\t"
                                     ++ "when checking defintion of " ++ x)
     u <- getSubst
     tysch <- closeTy kctx ictx (foldr (.) id (map (uncurry subst) u) ty)
     let ictx' = (string2Name x, tysch) : ictx
     return (kctx,ictx')

tiDec (Data (UIdent tc) is dAlts) (kctx,ictx) =
  do kArgSigs <- sequence $
                   do i <- is -- list monad
                      return $ case i of
                        IVarR(LIdent a) -> (,) (string2Name a) <$>
                                               (Right . Var <$> fresh "k")
                        IVarL(LIdent a) -> (,) (string2Name a) <$>
                                               (Left .  Var <$> fresh "i")
     let kArgSigsR = [ (x,k) | (x,Right k) <- kArgSigs]
     let kArgSigsL = [ (x,bind [] t) | (x,Left t)  <- kArgSigs]
     mapM (kiDAlt (kArgSigsR ++ kctx) (kArgSigsL ++ ictx)) dAlts
     let kctx' = (string2Name tc, foldr KArr Star (map snd kArgSigs)) : kctx
     u <- getSubst
     ictx' <- (++ ictx) <$>
                  sequence
                    [ (,) (string2Name c) <$>
                          closeTy kctx' ictx
                             (foldr (.) id (map (uncurry subst) u) 
                                    (foldr TArr retTy $ map type2Ty ts))
                     | DAlt (UIdent c) ts <- dAlts ] 
     return (kctx',ictx')
  where
  retTy = foldl TApp (TCon(string2Name tc)) $
                     do i <- is -- list monad
                        return $ case i of
                          IVarR(LIdent a) -> Right $ Var(string2Name a)
                          IVarL(LIdent a) -> Left  $ Var(string2Name a)

tiDec (Gadt (UIdent tc) as k gAlts) (kctx,ictx) =
  do kArgSigs <- sequence $
                   do i <- as -- list monad
                      return $ case i of
                        IVarR(LIdent a) -> (,) (string2Name a) <$>
                                               (Right . Var <$> fresh "k")
                        IVarL(LIdent a) -> (,) (string2Name a) <$>
                                               (Left .  Var <$> fresh "i")
     let kArgSigsR = [ (x,k) | (x,Right k) <- kArgSigs]
     let kArgSigsL = [ (x,bind [] t) | (x,Left t)  <- kArgSigs]
     let tcSig = (string2Name tc, foldr KArr (kind2Ki k) (map snd kArgSigs))
     mapM (kiGAlt tcSig as' (kArgSigsR ++ kctx) (kArgSigsL ++ ictx)) gAlts
     let kctx' = tcSig : kctx
     u <- getSubst
     ictx' <- (++ ictx) <$>
                  sequence
                    [ (,) (string2Name c) <$>
                          closeTy kctx' ictx
                            (foldr (.) id (map (uncurry subst) u) (type2Ty ty))
                     | GAlt (UIdent c) ty <- gAlts ]
     return (kctx',ictx')
  where
  as' = do i <- as
           return $ case i of IVarR(LIdent a) -> Right $ Var (string2Name a)
                              IVarL(LIdent a) -> Left  $ Var (string2Name a)

kiDAlt :: KCtx -> Ctx -> DataAlt -> KI ()
kiDAlt kctx ictx (DAlt _ ts) =
  do ks <- mapM (ki kctx ictx) (map type2Ty ts)
     lift $ unifyMany (zip (repeat Star) ks)

kiGAlt :: (TyName, Ki) -> [TArg] -> KCtx -> Ctx -> GadtAlt -> KI ()
kiGAlt (tc,kappa) as kctx ictx (GAlt (UIdent c) t) =
  do unless (length as < length resTyUnfold)
            (throwError . strMsg $ "need more args for "++show resTyUnfold++" the result type of "++c)
     unless (and (zipWith aeq (Right(TCon tc) : as) resTyUnfold))
            (throwError . strMsg $ "result type param args not uniform in "++c)
     kctx' <- (++ kctx) <$> sequence [(,) x <$> freshKi | x <- fvTy]
     ictx' <- (++ ictx) <$> sequence [(,) x <$> freshTy | x <- fvTm]
     k <- ki ((tc,kappa):kctx') ictx' resTy
     ks <- mapM (ki kctx' ictx') ts
     lift $ unifyMany (zip (repeat Star) (k:ks))
  where
  ty = type2Ty t
  (resTy:ts) = reverse (unfoldTArr ty)
  resTyUnfold = unfoldTApp resTy
  fvAll = nub (fv ty \\ fv as) \\ (tc : fv kctx ++ fv ictx)
  fvTm = nub (fvTmInTy ty \\ fv as) \\ (tc : fv kctx ++ fv ictx)
  fvTy = fvAll \\ fvTm
  freshKi = Var <$> fresh "k"
  freshTy = (bind [] . Var <$> fresh "a")

evDecs ctx (Data _ _ _ : ds)       = evDecs ctx ds
evDecs ctx (Gadt _ _ _ _ : ds)     = evDecs ctx ds
evDecs ctx (Def (LIdent x) t : ds) = do v <- ev ctx (term2Tm t)
                                        evDecs ((string2Name x, v) : ctx) ds
evDecs ctx []                      = return ctx

