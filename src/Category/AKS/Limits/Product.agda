{-# OPTIONS --without-K #-}

open import Lib
open import Category.AKS.Core

module Category.AKS.Limits.Product {i} {j} (𝓒 : Precategory {i} {j}) where

record has-cone (A B : / 𝓒 /) (Z : / 𝓒 /) : Type j where
  constructor cone
  field
    π₀ : 𝓒 [ Z , A ]
    π₁ : 𝓒 [ Z , B ]

ProductCone : (A B : / 𝓒 /) → Type (i ⊔ j)
ProductCone A B = Σ / 𝓒 / (has-cone A B)

is-universal : {A B : / 𝓒 /} → ProductCone A B → Type (i ⊔ lsucc j)
is-universal {A} {B} (Z , c) = (X : / 𝓒 /) → (𝓒 [ X , Z ]) == has-cone A B X

has-products : Type (i ⊔ lsucc j)
has-products = (A B : / 𝓒 /) → Σ (ProductCone A B) is-universal

