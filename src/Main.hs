-- vim: sw=2: ts=2: set expandtab:
{-# LANGUAGE CPP, TemplateHaskell, QuasiQuotes, NoMonomorphismRestriction #-}
-----------------------------------------------------------------------------
--
-- Module      :  Main
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

module Main (
    main
) where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Error
import Control.Monad.Identity
import Data.List (stripPrefix)
import System.Exit (exitFailure)
import Test.QuickCheck.All (quickCheckAll)
import Language.LBNF.Runtime (printTree)
import Generics.RepLib.Unify
import Unbound.LocallyNameless (runFreshMT)
import Syntax
import Infer
import InferDec
import Parser

k :: Kind
k = [kind| * |]

t = [type| a -> a |]

program =
   [prog|
    data Unit = Unit ;
    data Bool = False | True ;
    data Maybe a = Nothing | Just a ;
    data Either a b = Left a | Right b ;
    data Pair a b = Pair a b ;
    data N r = Z | S r ;
    data L a r = N | C a r ;
    data P r a = PN | PC a (r (Pair a a)) ;
    data MM = MM (Mu N);
    data MMM a = MMM (Mu P a);
    id = \x -> x ;
    x = id;
    z = {True -> True; False -> False};
    z2 = {Nothing -> False; Just x -> True};
    b = True ;
    c = x b;
    p = Pair ;
    z3 = Pair True False;
    zero = In 0 Z ;
    succ = \n -> In 0 (S n) ;
    nil = In 0 N ;
    cons = \x -> \xs -> In 0 (C x xs) ;
    pnil = In 1 PN ;
    pcons = \x -> \xs -> In 1 (PC x xs) ;
    -- ppnil = In 0 PN ;
    one = succ zero ;
    two = succ one ;
    three = succ two ;
    z5 = cons nil nil ;
    z6 = cons True nil ;
    z7 = pcons True (pcons (Pair False True) pnil) ;
    z8 = pcons one (pcons (Pair two three) pnil) ;
    flip = \f -> \x -> \y -> f y x;
    plus = mit add { Z   -> \m -> m
                   ; S n -> \m -> succ (add n m) } ;
    length = mit len { N -> zero; C x xs -> succ (len xs) } ;
    psum = mit sum {{ a . (a -> Mu N) -> Mu N }}
            { PN      -> \f -> zero
            ; PC x xs -> \f -> plus (f x)
                                    (sum xs {Pair a b -> plus (f a) (f b)} )
            } ;
    n4 = plus (plus one one) (plus one one) ;
    n5 = length z6 ;
    n6 = length z5 ;
    n7 = psum z8 id ;
    n8 = flip psum
   |]

{-
    succ = \n -> In 0 (S n)
    data M = MM (Mu N);
    x = \x -> x;
    y = x;
    z = {True -> True; False -> False};
    z2 = {Nothing -> False; Just x -> True};
    z3 = Pair True False;
    z4 = In 0 Z
 -}
    -- data Nat = Nat (Mu N) ;
    -- x2 = {True -> False; Unit -> True}
-- to print above
-- putStrLn $ Language.LBNF.Runtime.printTree d


kctx = case (runTI $ kiDataDecs (case program of Prog ds -> [d | d@(Data _ _ _)<- ds]) [])
         of Right x -> x
            Left x -> error x

ctx = case (runTI $ tiDecs kctx (case program of Prog ds -> [d | d@(Data _ _ _)<- ds]) [])
         of Right x -> x
            Left x -> error x

evctx = case (runFreshMT $ evDecs [] (case program of Prog ds -> ds)) 
          of Right x -> x
             Left x -> error x

-- Simple function to create a hello message.
hello s = "Hello " ++ s

-- Tell QuickCheck that if you strip "Hello " from the start of
-- hello s you will be left with s (for any s).
prop_hello s = stripPrefix "Hello " (hello s) == Just s



-- Hello World
exeMain = do
  mapM_ putStrLn
      $ reverse [show x++" : "++ printTree(ki2Kind k) | (x,k) <- kctx]
  putStrLn ""
  mapM_ putStrLn
      $ reverse [show x++" : "++ printTree(ty2Type $ (foldr (.) id (map (uncurry subst) u)) $ unbindTySch t) | (x,t) <- ctx]
  putStrLn ""
  mapM_ putStrLn
      $ reverse [show x++" = "++ printTree(tm2Term t) ++ " ;" | (x,t) <- evctx]
  putStrLn ""
  where
    Prog ds = program
    dataDecs = [d | d@(Data _ _ _)<- ds]
    kctx = case (runTI $ kiDataDecs dataDecs []) of
            Left errMsg -> error errMsg
            Right kctx -> kctx
    (ctx,u) = case (runTI $ do { ctx <- tiDecs kctx ds []
                               ; u<-getSubst; return (ctx,u)}) of
                Left errMsg -> error errMsg
                Right ctx -> ctx
    evctx = case (runFreshMT $ evDecs [] (case program of Prog ds -> ds)) of
              Right x -> x
              Left x -> error x




-- Entry point for unit tests.
testMain = do
    allPass <- $quickCheckAll -- Run QuickCheck on all prop_ functions
    unless allPass exitFailure

-- This is a clunky, but portable, way to use the same Main module file
-- for both an application and for unit tests.
-- MAIN_FUNCTION is preprocessor macro set to exeMain or testMain.
-- That way we can use the same file for both an application and for tests.
#ifndef MAIN_FUNCTION
#define MAIN_FUNCTION exeMain
#endif
main = MAIN_FUNCTION

{-
*Main> runTI $ ki kctx (type2Ty [type| Pair Bool |])
Right (KVar k)
*Main> let Right k = it
*Main> runTI $ ki kctx (type2Ty [type| Pair Bool |]) >> getSubst 
Right [(k,KArr Star Star)]
*Main> let Right u = it
-}
