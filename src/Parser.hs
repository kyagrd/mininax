-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
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
import Unbound.LocallyNameless
     ( string2Name, name2String, bind, unbind, embed, Embed(..) )
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import qualified Syntax as S

{-
bnfc [lbnf|
RAlt.  Reg1 ::= Reg1 "|" Reg2;
RSeq.  Reg2 ::= Reg2 Reg3;
RStar. Reg3 ::= Reg3 "*";
REps.  Reg3 ::= "eps";
RChar. Reg3 ::= Char;
_. Reg  ::= Reg1;
_. Reg1 ::= Reg2;
_. Reg2 ::= Reg3;
_. Reg3 ::= "(" Reg ")";
|] -}

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
TFix. Type2 ::= "Mu" Type2 ;
coercions Type 3 ;

Var. Term3 ::= LIdent ;
Con. Term3 ::= UIdent ;
In . Term2 ::= "In" Integer Term2 ;
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

Prog. Prog ::= [Dec]
|]


instance Print S.Ki where
  prt n = prt n . ki2Kind
  prtList = prtList . map ki2Kind

instance Print S.Ty where
  prt n = prt n . ty2Type
  prtList = prtList . map ty2Type

instance Print S.Tm where
  prt n = prt n . tm2Term
  prtList = prtList . map tm2Term


-- Translating between BNFC syntax and Unbound syntax

kind2Ki KStar = S.Star
kind2Ki (KVar (LIdent s)) = S.KVar (string2Name s)
kind2Ki (KArr k1 k2) = S.KArr (kind2Ki k1) (kind2Ki k2)

ki2Kind S.Star = KStar
ki2Kind (S.KVar nm) = KVar (LIdent $ name2String nm)
ki2Kind (S.KArr k1 k2) = KArr (ki2Kind k1) (ki2Kind k2)


type2Ty (TVar (LIdent s)) = S.TVar (string2Name s)
type2Ty (TCon (UIdent s)) = S.TCon (string2Name s)
type2Ty (TArr t1 t2) = S.TArr (type2Ty t1) (type2Ty t2)
type2Ty (TApp t1 t2) = S.TApp (type2Ty t1) (type2Ty t2)
type2Ty (TFix t) = S.TFix (type2Ty t)

ty2Type (S.TVar nm) = TVar (LIdent $ name2String nm)
ty2Type (S.TCon nm) = TCon (UIdent $ name2String nm)
ty2Type (S.TArr t1 t2) = TArr (ty2Type t1) (ty2Type t2)
ty2Type (S.TApp t1 t2) = TApp (ty2Type t1) (ty2Type t2)
ty2Type (S.TFix t) = TFix (ty2Type t)


term2Tm (Var (LIdent s)) = S.Var (string2Name s)
term2Tm (Con (UIdent s)) = S.Con (string2Name s)
term2Tm (In n e) = S.In n (term2Tm e)
term2Tm (Lam (LIdent s) e) = S.Lam (bind (string2Name s) (term2Tm e))
term2Tm (App e1 e2) = S.App (term2Tm e1) (term2Tm e2)
term2Tm (Let (LIdent s) e1 e2) = S.Let (bind (string2Name s, embed (term2Tm e1))
                                             (term2Tm e2))
term2Tm (Alt cs) = S.Alt Nothing
        [ (string2Name c, bind [string2Name s | LIdent s <- as] (term2Tm e))
         | Case (UIdent c) as e <- cs ]
term2Tm (AltAnn (Phi xs ty) cs) =
  S.Alt (Just $ bind [string2Name s | LIdent s <- xs] (type2Ty ty))
        [ (string2Name c, bind [string2Name s | LIdent s <- as] (term2Tm e))
         | Case (UIdent c) as e <- cs ]


tm2Term (S.Var nm) = Var (LIdent $ name2String nm)
tm2Term (S.Con nm) = Con (UIdent $ name2String nm)
tm2Term (S.In n e) = In n (tm2Term e)
tm2Term (S.Lam bnd) = Lam (LIdent $ name2String nm) (tm2Term e)
          where (nm,e) = unsafeUnbind bnd
tm2Term (S.App e1 e2) = App (tm2Term e1) (tm2Term e2)
tm2Term (S.Let bnd) = Let (LIdent $ name2String nm) (tm2Term e1) (tm2Term e2)
          where ((nm,Embed e1),e2) = unsafeUnbind bnd
tm2Term (S.Alt Nothing cs) =
  Alt [ Case (UIdent c) (map (LIdent . name2String) as) (tm2Term e)
      | (c,(as,e)) <- map (\(nm,bnd) -> (name2String nm, unsafeUnbind bnd)) cs ]
tm2Term (S.Alt (Just phi) cs) =
  AltAnn (Phi (map (LIdent . name2String) nms) (ty2Type ty))
      [ Case (UIdent c) (map (LIdent . name2String) as) (tm2Term e)
      | (c,(as,e)) <- map (\(nm,bnd) -> (name2String nm, unsafeUnbind bnd)) cs ]
  where
  (nms,ty) = unsafeUnbind phi

