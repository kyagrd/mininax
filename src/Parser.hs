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
_. Kind  ::= Kind1 ;
_. Kind1 ::= Kind2 ;
_. Kind2 ::= "(" Kind ")" ;

TVar. Type3 ::= LIdent ;
TCon. Type3 ::= UIdent ;
TArr. Type1 ::= Type2 "->" Type1 ;
TApp. Type2 ::= Type3 Type2 ;
_. Type  ::= Type1 ;
_. Type1 ::= Type2 ;
_. Type2 ::= Type3 ;
_. Type3 ::= "(" Type ")" ;

Var. Term3 ::= LIdent ;
Con. Term3 ::= UIdent ;
Lam. Term1 ::= "\\" LIdent "->" Term1 ;
App. Term2 ::= Term3 Term2 ;
Let. Term1 ::= "let" LIdent "=" Term1 "in" Term1 ;
Alt. Term3 ::= "{" "}" ;
_. Term  ::= Term1 ;
_. Term1 ::= Term2 ;
_. Term2 ::= Term3 ;
_. Term3 ::= "(" Term ")"
|]
