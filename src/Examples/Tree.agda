{-# OPTIONS --without-K #-}

module Examples.Tree where

open import Lib

module _
  (_/_ : (A : Set) (R : A → A → Set) → Set)
  ([_] : {A : Set} {R : A → A → Set} → A → A / R)
  (quot : {A : Set} {R : A → A → Set} (x y : A) → R x y → [_] {A} {R} x == [ y ])
  (quot-elim :
    (A : Set)
    (R : A → A → Set)
    (B : A / R → Set)
    (m-proj : (a : A) → B [ a ])
    (m-quot : (a b : A) (p : R a b) → {!transport !} == {!!})
    → (x : A / R) → B x)
  where
