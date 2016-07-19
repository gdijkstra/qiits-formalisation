{-# OPTIONS --without-K #-}

module Category.AKS.Functor where

open import Lib
open import Category.AKS.Core

record Functor {i j k l} (𝓒 : Precategory {i} {j}) (𝓓 : Precategory {k} {l}) : Type (i ⊔ j ⊔ k ⊔ l) where
  field
    obj : / 𝓒 / → / 𝓓 /
    hom : {x y : / 𝓒 /} → 𝓒 [ x , y ] → 𝓓 [ obj x , obj y ]
    id : {x : / 𝓒 /} → hom (𝟙 𝓒 x) == 𝟙 𝓓 (obj x)
    comp : {x y z : / 𝓒 /} (g : 𝓒 [ y , z ]) (f : 𝓒 [ x , y ]) → hom (g ∘[ 𝓒 ] f) == (hom g ∘[ 𝓓 ] hom f)

_⇒_ : {i j k l : ULevel} → Precategory {i} {j} → Precategory {k} {l} → Type (i ⊔ j ⊔ k ⊔ l)
𝓒 ⇒ 𝓓 = Functor 𝓒 𝓓

