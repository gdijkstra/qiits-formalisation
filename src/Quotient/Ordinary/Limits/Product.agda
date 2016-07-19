{-# OPTIONS --without-K #-}

open import Category.AKS
open import Category.AKS.Limits

module Quotient.Ordinary.Limits.Product {i} {j} (𝓒 : Precategory {i} {j}) (F : 𝓒 ⇒ 𝓒) (𝓒-has-products : has-products 𝓒) where

open import Lib
open import Quotient.Ordinary.Core 𝓒 F

_×[𝓒]_ : / 𝓒 / → / 𝓒 / → / 𝓒 /
X ×[𝓒] Y with 𝓒-has-products X Y
X ×[𝓒] Y | (X×Y , _) , _ = X×Y



alg-has-products : has-products Alg
alg-has-products (alg X θ) (alg Y ρ) = ((alg (X ×[𝓒] Y) {!!}) , {!!}) , {!!}
