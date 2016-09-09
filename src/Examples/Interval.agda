{-# OPTIONS --without-K #-}

open import Lib

module Examples.Interval where

{-# BUILTIN REWRITE _==_ #-}

postulate
  I : Type₀
  zero : I
  one : I
  seg : zero == one

-- The motive for I is just I → Type

record IntervalMethods (P : I → Type₀) : Type₀ where
  field
    m-zero : P zero
    m-one : P one
    --m-seg : m-zero == m-one [ P ↓ seg ]

module _ (P : I → Type₀) (𝓜 : IntervalMethods P) where
  open IntervalMethods 𝓜

  postulate
    ind-I : (x : I) → P x
    ind-I-zero : ind-I zero == m-zero
    ind-I-one : ind-I one == m-one
    --ind-I-seg : apd ind-I seg == mseg

