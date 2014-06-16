-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE QuasiQuotes, TemplateHaskell,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             CPP
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

import Language.LBNF hiding (printTree)
import Language.LBNF.Runtime (Doc)
import Unbound.LocallyNameless hiding (Con, Data)
import Unbound.LocallyNameless.Ops (unsafeUnbind)
import Syntax (Ki, Ty, Tm, PSUT, isKi, isTy, isTm)
import qualified Syntax as S
import Control.Applicative
import System.IO
import Data.Char
-- import Debug.Trace
trace _ a = a


-- antiquote "[" ":" ":]" ;
bnfc [lbnf|

token LIdent ( ('`' | lower | '_') (letter | digit | '_' | '\'')* ) ;
token UIdent (upper (letter | digit | '_' | '\'')* ) ;

Prog. Prog ::= [Dec] ;

KVar.  Kind2 ::= LIdent ;
KStar. Kind2 ::= "*" ;
KArr.  Kind1 ::= KArg "->" Kind1 ;
coercions Kind 2 ;

KArgL. KArg ::= "{" Type "}" ;
KArgR. KArg ::= Kind2 ;

TVar. Type3 ::= LIdent ;
TCon. Type3 ::= UIdent ;
TArr. Type1 ::= Type2 "->" Type1 ;
TApp. Type2 ::= Type2 TArg;
TFix. Type2 ::= "Mu" Type3 ;
coercions Type 3 ;

TArgL. TArg ::= "{" Term "}" ;
TArgR. TArg ::= Type3 ;

Var.    Term3 ::= LIdent ;
Con.    Term3 ::= UIdent ;
In .    Term2 ::= "In" Integer Term3 ;
MIt.    Term2 ::= "mit" LIdent "{" [Alt] "}" ;
MItAnn. Term2 ::= "mit" LIdent "{{" IxMap "}}" "{" [Alt] "}" ;
MPr.    Term2 ::= "mpr" LIdent LIdent "{" [Alt] "}" ;
MPrAnn. Term2 ::= "mpr" LIdent LIdent "{{" IxMap "}}" "{" [Alt] "}" ;
Lam.    Term1 ::= "\\" LIdent "->" Term1 ;
App.    Term2 ::= Term2 Term3 ;
Let.    Term1 ::= "let" LIdent "=" Term1 "in" Term1 ;
Alt.    Term3 ::= "{" [Alt] "}" ;
AltAnn. Term3 ::= "{{" IxMap "}}" "{" [Alt] "}" ;
coercions Term 3 ;

Case. Alt ::= UIdent [LIdent] "->" Term ;
separator Alt ";" ;

Phi. IxMap ::= [IVar] "." Type ;

IVarR. IVar ::= LIdent ;
IVarL. IVar ::= "{" LIdent "}" ;

[].  [IVar] ::= ;
(:). [IVar] ::= IVar [IVar] ;

[].  [LIdent] ::= ;
(:). [LIdent] ::= LIdent [LIdent] ;

[].  [Type3] ::= ;
(:). [Type3] ::= Type3 [Type3] ;

Gadt. Dec ::= "data" UIdent [IVar] ":" Kind "where" "{" [GadtAlt] "}" ;
Data. Dec ::= "data" UIdent [IVar] "=" [DataAlt] ;
Def.  Dec ::= LIdent "=" Term ;
separator Dec ";" ;

GAlt. GadtAlt ::= UIdent ":" Type ;
separator GadtAlt ";";

DAlt. DataAlt ::= UIdent [Type3] ;
separator DataAlt "|";

comment "{-" "-}" ;
comment "--" ; 
     |]
-- entrypoints Prog, Dec, Kind, Type, Term ;


instance Print S.PSUT where
  prt n x | isKi x = prt n (ki2Kind x)
          | isTy x = prt n (ty2Type x)
          | isTm x = prt n (tm2Term x)
  prtList xs@(x:_)
          | isKi x = prtList (map ki2Kind xs)
          | isTy x = prtList (map ty2Type xs)
          | isTm x = prtList (map tm2Term xs)
  prtList []            = prtList ([]::[Integer])

-- instance Print Ki where
--   prt n = prt n . ki2Kind
--   prtList = prtList . map ki2Kind
-- 
-- instance Print Ty where
--   prt n = prt n . ty2Type
--   prtList = prtList . map ty2Type
-- 
-- instance Print Tm where
--   prt n = prt n . tm2Term
--   prtList = prtList . map tm2Term

-- Translating between BNFC syntax and Unbound syntax

kind2Ki KStar = S.Star
kind2Ki (KVar (LIdent s)) = S.Var (string2Name s)
kind2Ki (KArr (KArgR k1) k2) = S.KArr (Right $ kind2Ki k1) (kind2Ki k2)
kind2Ki (KArr (KArgL t1) k2) = S.KArr (Left  $ type2Ty t1) (kind2Ki k2)


ki2Kind S.Star = KStar
ki2Kind (S.Var nm) = KVar (LIdent $ show nm)
ki2Kind (S.KArr (Right k1) k2) = KArr (KArgR $ ki2Kind k1) (ki2Kind k2)
ki2Kind (S.KArr (Left  t1) k2) = KArr (KArgL $ ty2Type t1) (ki2Kind k2)


type2Ty (TVar (LIdent s)) = S.Var (string2Name s)
type2Ty (TCon (UIdent s)) = S.TCon (string2Name s)
type2Ty (TArr t1 t2) = S.TArr (type2Ty t1) (type2Ty t2)
type2Ty (TApp t1 (TArgR t2)) = S.TApp (type2Ty t1) (Right $ type2Ty t2)
type2Ty (TApp t1 (TArgL e2)) = S.TApp (type2Ty t1) (Left  $ term2Tm e2)
type2Ty (TFix t) = S.TFix (type2Ty t)

ty2Type (S.Var nm) = TVar (LIdent $ show nm)
ty2Type (S.TCon nm) = TCon (UIdent $ show nm)
ty2Type (S.TArr t1 t2) = TArr (ty2Type t1) (ty2Type t2)
ty2Type (S.TApp t1 (Right t2)) = TApp (ty2Type t1) (TArgR $ ty2Type t2)
ty2Type (S.TApp t1 (Left  e2)) = TApp (ty2Type t1) (TArgL $ tm2Term e2)
ty2Type (S.TFix t) = TFix (ty2Type t)


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
  S.Alt (Just $ bind (map ident2names xs) (type2Ty ty))
        [ (string2Name c, bind [string2Name s | LIdent s <- as] (term2Tm e))
         | Case (UIdent c) as e <- cs ]
  where
  ident2names (IVarR (LIdent s)) = Right (string2Name s)
  ident2names (IVarL (LIdent s)) = Left  (string2Name s)

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
  AltAnn (Phi (map names2ident nms) (ty2Type ty))
      [ Case (UIdent c) (map (LIdent . show) as) (tm2Term e)
      | (c,(as,e)) <- map (\(nm,bnd) -> (show nm, unsafeUnbind bnd)) cs ]
  where
  (nms,ty) = unsafeUnbind phi
  names2ident (Right nm) = IVarR (LIdent $ show nm)
  names2ident (Left  nm) = IVarL (LIdent $ show nm)
tm2Term t = Con(UIdent $ printTree t)


hTokens h = tokens <$> hGetContents h

hProg h = pProg <$> hTokens h


------------------------------------------------------

-- -- * Overloaded pretty-printer
printTree :: Print a => a -> String
printTree = render . prt 0

render :: Doc -> String
render = renderN 0

renderN n d = rend n (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts ->
        let rendDefault = showChar '{' . new (i+1) . rend (i+1) ts
            (ts1, ts2) = break (=="}") ts
        in if (null ts2 || elem "{" ts1 || elem ";" ts1) 
             then rendDefault
             else case ts2 of
                    "}":";":ts' -> showChar '{' . rend i ts1 . space "}" .
                                   showChar ';' . new i . rend i ts'
                    "}"    :ts' ->
                               let rend_ts1 = case ts1 of 
                                                []  -> id 
                                                [t] -> showString t
                                                _   -> rend i ts1
                                in showChar '{' . rend_ts1 . space "}" .
                                   rend i ts'
                    _ -> rendDefault
    "}" : ";":ts -> new (i-1) . showChar '}' . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : "," :ts -> showString t . space "," . rend i ts
    t  : ")" :ts@(")":_) -> showString t . showChar ')' . rend i ts
    t  : ")" :ts@("}":_) -> showString t . showChar ')' . rend i ts
    t  : ")" :[]         -> showString t . showChar ')'
    t  : ")" :ts         -> showString t . space ")" . rend i ts
    t  : "]" :ts -> showString t . showChar ']' . rend i ts
    t        :[] -> showString t
    t        :ts -> space t . rend i ts
    _            -> id
  new i   = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t = showString t . (\s -> if null s then "" else (' ':s))


concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

------------------------------------------------------
instance Show PSUT where show = printTree

instance Alpha PSUT where

instance Subst PSUT PSUT where
  isvar (S.Var x) = Just (SubstName x)
  -- isvar (S.TCon x) = Just (SubstName x)
  -- isvar (S.Con x) = Just (SubstName x)
  isvar _ = Nothing

