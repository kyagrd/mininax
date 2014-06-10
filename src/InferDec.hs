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
import Infer hiding (trace)

import Data.Char
import Data.List
import Data.Either
import Control.Monad
import Control.Monad.Error
import Control.Monad.Trans
import Control.Applicative
import Generics.RepLib.Unify (subst)
import Unbound.LocallyNameless ( bind, fresh, string2Name, aeq, fv )
import qualified Unbound.LocallyNameless as LN
import GHC.Exts( IsString(..) )
-- import Debug.Trace
trace _ a = a

-- TODO check uniqueness of TCon and Con names (not yet checking uniqueness?)

tiDecs ds = foldl1 (>=>) (map tiDec ds)

-- TODO not checking wheter there are TyName with backquote in t
-- it should be only TmName inside { } which can be backquote var
-- I think current implementation does catch this kind of error eventually
-- but I expect that the error message would be misterious
type2Ty' env t = foldr (.) id (map (uncurry LN.subst) env') (type2Ty t)
               where
               env' = [(string2Name('`':show x)::TmName,t) | (x,t) <-env]

term2Tm' env t = foldr (.) id (map (uncurry LN.subst) env') (term2Tm t)
               where
               env' = [(string2Name('`':show x)::TmName,t) | (x,t) <-env]



tiDec :: Dec -> (KCtx,Ctx,Env) -> TI (KCtx,Ctx,Env)
tiDec (Def (LIdent x) t) (kctx,ictx,env)
  | head x == '`' = throwError(strMsg $ show x++
                                      " backquoted variable not allowed")
tiDec (Def (LIdent x) t) (kctx,ictx,env) =
  do ty <- ti kctx ictx [] env (term2Tm' env t)
           `catchError`
           (\e -> throwError . strMsg $ e ++ "\n\t"
                                     ++ "when checking defintion of " ++ x)
     u <- getSubst
     tysch <- closeTy kctx (filter (isUpper.head.show.fst) ictx) (foldr (.) id (map (uncurry subst) u) ty)
     let ictx' = (string2Name x, tysch) : ictx
         env'  = ( string2Name x -- lambda lifting (make all global def closed)
                 , foldr (.) id (map (uncurry subst) env) (term2Tm t) ) : env
     return (kctx,ictx',env')

tiDec (Data (UIdent tc) is dAlts) (kctx,ictx,env) =
  do kArgSigs <- sequence $
                   do i <- is -- list monad
                      return $ case i of
                        IVarR(LIdent a) -> (,) (string2Name a) <$>
                                               (Right . Var <$> fresh "k")
                        IVarL(LIdent a) -> (,) (string2Name a) <$>
                                               (Left .  Var <$> fresh "i")
     let kArgSigsR = [ (x,k) | (x,Right k) <- kArgSigs]
     let kArgSigsL = [ (x,bind [] t) | (x,Left t)  <- kArgSigs]
     mapM (kiDAlt (kArgSigsR ++ kctx) (kArgSigsL ++ ictx) env) dAlts
     let kctx' = (string2Name tc, foldr KArr Star (map snd kArgSigs)) : kctx
     u <- getSubst
     ictx' <- (++ ictx) <$>
                  sequence
                    [ (,) (string2Name c) <$>
                          closeTy kctx' (filter (isUpper.head.show.fst) ictx)
                             (foldr (.) id (map (uncurry subst) u) 
                                    (foldr TArr retTy $ map (type2Ty' env) ts))
                     | DAlt (UIdent c) ts <- dAlts ] 
     return (kctx',ictx',env)
  where
  retTy = foldl TApp (TCon(string2Name tc)) $
                     do i <- is -- list monad
                        return $ case i of
                          IVarR(LIdent a) -> Right $ Var(string2Name a)
                          IVarL(LIdent a) -> Left  $ Var(string2Name a)

tiDec (Gadt (UIdent tc) as k gAlts) (kctx,ictx,env) = trace tc $
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
     mapM (kiGAlt tcSig as' (kArgSigsR ++ kctx) (kArgSigsL ++ ictx) env) gAlts
     let kctx' = tcSig : kctx
     u <- getSubst
     ictx' <- (++ ictx) <$>
                  sequence
                    [ (,) (string2Name c) <$>
                          closeTy kctx' (filter (isUpper.head.show.fst) ictx)
                            (foldr (.) id (map (uncurry subst) u)
                                   (type2Ty' env ty))
                     | GAlt (UIdent c) ty <- gAlts ]
     return (kctx',ictx',env)
  where
  as' = do i <- as
           return $ case i of IVarR(LIdent a) -> Right $ Var (string2Name a)
                              IVarL(LIdent a) -> Left  $ Var (string2Name a)

kiDAlt :: KCtx -> Ctx -> Env -> DataAlt -> KI ()
kiDAlt kctx ictx env (DAlt _ ts) =
  do ks <- mapM (ki kctx ictx env) (map (type2Ty' env) ts)
     lift $ unifyMany (zip (repeat Star) ks)
  where

kiGAlt :: (TyName, Ki) -> [TArg] -> KCtx -> Ctx -> Env -> GadtAlt -> KI ()
kiGAlt (tc,kappa) as kctx ictx env (GAlt (UIdent c) t) = trace (c++","++show ty) $
  do unless (length as < length resTyUnfold)
            (throwError . strMsg $ "need more args for "++show resTyUnfold++" the result type of "++c)
     unless (and (zipWith aeq (Right(TCon tc) : as) resTyUnfold))
            (throwError . strMsg $ "result type param args not uniform in "++c)
     kctx' <- (++ kctx) <$> sequence [(,) x <$> freshKi | x <- fvTy]
     ictx' <- (++ ictx) <$> sequence [(,) x <$> freshTy | x <- fvTm]
     k <- ki ((tc,kappa):kctx') ictx' env resTy
     ks <- mapM (ki kctx' ictx' env) ts
     lift $ unifyMany (zip (repeat Star) (k:ks))
  where
  ty = type2Ty' env t
  (resTy:ts) = reverse (unfoldTArr ty)
  resTyUnfold = unfoldTApp resTy
  fvAll = nub (fv ty \\ fv as) \\ [tc]
  fvTm = nub (fvTmInTy ty \\ fv as) \\ [tc]
  fvTy = fvAll \\ fvTm
  freshKi = Var <$> fresh "k"
  freshTy = (bind [] . Var <$> fresh "a")

evDecs env (Data _ _ _ : ds)       = evDecs env ds
evDecs env (Gadt _ _ _ _ : ds)     = evDecs env ds
evDecs env (Def (LIdent x) t : ds) = do v <- ev env (term2Tm t)
                                        -- v <- norm env (term2Tm t)
                                        evDecs ((string2Name x, v) : env) ds
evDecs env []                      = return env

