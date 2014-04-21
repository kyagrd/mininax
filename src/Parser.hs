-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE QuasiQuotes, TemplateHaskell,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances
  #-}
-----------------------------------------------------------------------------
--
-- Module      :  Parser
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

module Parser where

import Language.LBNF
import Unbound.LocallyNameless hiding (Con, Data)
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import Syntax (Ki, Ty, Tm)
import qualified Syntax as S
import Control.Applicative
import System.IO

bnfc [lbnf|
antiquote "[" ":" ":]" ;

token LIdent (lower (letter | digit | '_')* ) ;
token UIdent (upper (letter | digit | '_')* ) ;

KVar.  Kind2 ::= LIdent ;
KStar. Kind2 ::= "*" ;
KArr.  Kind1 ::= Kind2 "->" Kind1 ;
coercions Kind 2 ;

TVar. Type3 ::= LIdent ;
TCon. Type3 ::= UIdent ;
TArr. Type1 ::= Type2 "->" Type1 ;
TApp. Type2 ::= Type2 Type3 ;
TFix. Type2 ::= "Mu" Type3 ;
coercions Type 3 ;

Var. Term3 ::= LIdent ;
Con. Term3 ::= UIdent ;
In . Term2 ::= "In" Integer Term2 ;
MIt . Term2 ::= "mit" LIdent "{" [Alt] "}" ;
MItAnn . Term2 ::= "mit" LIdent "{{" IxMap "}}" "{" [Alt] "}" ;
MPr . Term2 ::= "mpr" LIdent LIdent "{" [Alt] "}" ;
MPrAnn . Term2 ::= "mpr" LIdent LIdent "{{" IxMap "}}" "{" [Alt] "}" ;
Lam. Term1 ::= "\\" LIdent "->" Term1 ;
App. Term2 ::= Term2 Term3 ;
Let. Term1 ::= "let" LIdent "=" Term1 "in" Term1 ;
Alt. Term3 ::= "{" [Alt] "}" ;
AltAnn. Term3 ::= "{{" IxMap "}}" "{" [Alt] "}" ;
coercions Term 3 ;

Case. Alt ::= UIdent [LIdent] "->" Term ;
separator Alt ";" ;

Phi. IxMap ::= [LIdent] "." Type ;

[].  [LIdent] ::= ;
(:). [LIdent] ::= LIdent [LIdent] ;

[].  [Type3] ::= ;
(:). [Type3] ::= Type3 [Type3] ;

Data. Dec ::= "data" UIdent [LIdent] "=" [DataAlt] ;
Def.  Dec ::= LIdent "=" Term ;
separator Dec ";" ;

DAlt. DataAlt ::= UIdent [Type3] ;
separator DataAlt "|";

Prog. Prog ::= [Dec] ;

comment "--" ; 
comment "{-" "-}"
|]

instance Print Ki where
  prt n = prt n . ki2Kind
  prtList = prtList . map ki2Kind

instance Print Ty where
  prt n = prt n . ty2Type
  prtList = prtList . map ty2Type

instance Print Tm where
  prt n = prt n . tm2Term
  prtList = prtList . map tm2Term

-- Translating between BNFC syntax and Unbound syntax

kind2Ki KStar = S.Star
kind2Ki (KVar (LIdent s)) = S.KVar (string2Name s)
kind2Ki (KArr k1 k2) = S.KArr (kind2Ki k1) (kind2Ki k2)

ki2Kind S.Star = KStar
ki2Kind (S.KVar nm) = KVar (LIdent $ show nm)
ki2Kind (S.KArr k1 k2) = KArr (ki2Kind k1) (ki2Kind k2)


type2Ty (TVar (LIdent s)) = S.TVar (string2Name s)
type2Ty (TCon (UIdent s)) = S.TCon (string2Name s)
type2Ty (TArr t1 t2) = S.TArr (type2Ty t1) (type2Ty t2)
type2Ty (TApp t1 t2) = S.TApp (type2Ty t1) (type2Ty t2)
type2Ty (TFix t) = S.TFix (type2Ty t)

ty2Type (S.TVar nm) = TVar (LIdent $ show nm)
ty2Type (S.TCon nm) = TCon (UIdent $ show nm)
ty2Type (S.TArr t1 t2) = TArr (ty2Type t1) (ty2Type t2)
ty2Type (S.TApp t1 t2) = TApp (ty2Type t1) (ty2Type t2)
ty2Type (S.TFix t) = TFix (ty2Type t)


case2SAltItem (Case (UIdent c) xs e) =
    ( string2Name c, bind [string2Name x | LIdent x <- xs] (term2Tm e) )

phi2SPhi (Phi xs ty) = bind [string2Name s | LIdent s <- xs] (type2Ty ty)

term2Tm (Var (LIdent s)) = S.Var (string2Name s)
term2Tm (Con (UIdent s)) = S.Con (string2Name s)
term2Tm (In n e) = S.In n (term2Tm e)
term2Tm (MIt (LIdent f) as) =
  S.MIt $ bind (string2Name f) $ term2Tm (Alt as)
term2Tm (MItAnn (LIdent f) phi as) =
  S.MIt $ bind (string2Name f) $ term2Tm (AltAnn phi as)
term2Tm (MPr (LIdent f) (LIdent cast) as) =
  S.MPr $ bind (string2Name f, string2Name cast) $ term2Tm (Alt as)
term2Tm (MPrAnn (LIdent f) (LIdent cast) phi as) =
  S.MPr $ bind (string2Name f, string2Name cast) $ term2Tm (AltAnn phi as)
term2Tm (Lam (LIdent s) e) = S.Lam (bind (string2Name s) (term2Tm e))
term2Tm (App e1 e2) = S.App (term2Tm e1) (term2Tm e2)
term2Tm (Let (LIdent s) e1 e2) =
        S.Let (bind (string2Name s, embed (term2Tm e1)) (term2Tm e2))
term2Tm (Alt cs) = S.Alt Nothing
        [ (string2Name c, bind [string2Name s | LIdent s <- as] (term2Tm e))
         | Case (UIdent c) as e <- cs ]
term2Tm (AltAnn (Phi xs ty) cs) =
  S.Alt (Just $ bind [string2Name s | LIdent s <- xs] (type2Ty ty))
        [ (string2Name c, bind [string2Name s | LIdent s <- as] (term2Tm e))
         | Case (UIdent c) as e <- cs ]


tm2Term (S.Var nm) = Var (LIdent $ show nm)
tm2Term (S.Con nm) = Con (UIdent $ show nm)
tm2Term (S.In n e) = In n (tm2Term e)
tm2Term (S.MIt b) =
  case tm2Term sAlt of
    Alt cs        -> MIt    (LIdent $ show nm)     cs
    AltAnn phi cs -> MItAnn (LIdent $ show nm) phi cs
  where
  (nm,sAlt) = unsafeUnbind b
tm2Term (S.MPr b) =
  case tm2Term sAlt of
    Alt cs        -> MPr    (LIdent $ show nm1) (LIdent $ show nm2)     cs
    AltAnn phi cs -> MPrAnn (LIdent $ show nm1) (LIdent $ show nm2) phi cs
  where
  ((nm1,nm2),sAlt) = unsafeUnbind b
tm2Term (S.Lam bnd) = Lam (LIdent $ show nm) (tm2Term e)
          where (nm,e) = unsafeUnbind bnd
tm2Term (S.App e1 e2) = App (tm2Term e1) (tm2Term e2)
tm2Term (S.Let bnd) = Let (LIdent $ show nm) (tm2Term e1) (tm2Term e2)
          where ((nm,Embed e1),e2) = unsafeUnbind bnd
tm2Term (S.Alt Nothing cs) =
  Alt [ Case (UIdent c) (map (LIdent . show) as) (tm2Term e)
      | (c,(as,e)) <- map (\(nm,bnd) -> (show nm, unsafeUnbind bnd)) cs ]
tm2Term (S.Alt (Just phi) cs) =
  AltAnn (Phi (map (LIdent . show) nms) (ty2Type ty))
      [ Case (UIdent c) (map (LIdent . show) as) (tm2Term e)
      | (c,(as,e)) <- map (\(nm,bnd) -> (show nm, unsafeUnbind bnd)) cs ]
  where
  (nms,ty) = unsafeUnbind phi


hTokens h = tokens <$> hGetContents h

hProg h = pProg <$> hTokens h


------------------------------------------------------
instance Show Ki where show = printTree
instance Show Ty where show = printTree
instance Show Tm where show = printTree

instance Alpha Ki where
instance Alpha Ty where
instance Alpha Tm where

instance Subst Ki Ki where
  isvar (S.KVar x) = Just (SubstName x)
  isvar _ = Nothing
instance Subst Ty Ki where
instance Subst Ty Tm where
instance Subst Tm Ki where
instance Subst Tm Ty where
instance Subst Tm Tm where
  isvar (S.Var x) = Just (SubstName x)
  isvar (S.Con x) = Just (SubstName x)
  isvar _  = Nothing
instance Subst Ty Ty where
  isvar (S.TVar x) = Just (SubstName x)
  isvar (S.TCon x) = Just (SubstName x)
  isvar _ = Nothing


