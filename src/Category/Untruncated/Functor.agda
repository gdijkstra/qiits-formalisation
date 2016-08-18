{-# OPTIONS --without-K #-}

module Category.Untruncated.Functor where

open import Lib
open import Category.Untruncated.Core

record Functor {i j k l} (𝓒 : Precategory {i} {j}) (𝓓 : Precategory {k} {l}) : Type (i ⊔ j ⊔ k ⊔ l) where
  field
    obj : / 𝓒 / → / 𝓓 /
    hom : {x y : / 𝓒 /} → 𝓒 [ x , y ] → 𝓓 [ obj x , obj y ]
    id : {x : / 𝓒 /} → hom (Id 𝓒 x) == Id 𝓓 (obj x)
    comp : {x y z : / 𝓒 /} (g : 𝓒 [ y , z ]) (f : 𝓒 [ x , y ]) → hom (g ∘[ 𝓒 ] f) == (hom g ∘[ 𝓓 ] hom f)

_⇒_ : {i j k l : ULevel} → Precategory {i} {j} → Precategory {k} {l} → Type (i ⊔ j ⊔ k ⊔ l)
𝓒 ⇒ 𝓓 = Functor 𝓒 𝓓

_₀_ : {i j k l : ULevel} {𝓒 : Precategory {i} {j}} {𝓓 : Precategory {k} {l}} → Functor 𝓒 𝓓 → / 𝓒 / → / 𝓓 /
F ₀ X = Functor.obj F X

_₁_ : {i j k l : ULevel} {𝓒 : Precategory {i} {j} } {𝓓 : Precategory {k} {l}} → (F : Functor 𝓒 𝓓) {X Y : / 𝓒 /} → 𝓒 [ X , Y ] → 𝓓 [ F ₀ X , F ₀ Y ]
F ₁ f = Functor.hom F f

_-id_ : {i j k l : ULevel} {𝓒 : Precategory {i} {j} } {𝓓 : Precategory {k} {l}} → (F : Functor 𝓒 𝓓) → (X : / 𝓒 /) → (F ₁ (Id 𝓒 X)) == Id 𝓓 (F ₀ X)
F -id X = Functor.id F

_-∘ : {i j k l : ULevel} {𝓒 : Precategory {i} {j} } {𝓓 : Precategory {k} {l}} → (F : Functor 𝓒 𝓓)
  → {Y Z : / 𝓒 /} (g : 𝓒 [ Y , Z ])
  → {X : / 𝓒 /}   (f : 𝓒 [ X , Y ])
  → (F ₁ (g ∘[ 𝓒 ] f)) == ((F ₁ g) ∘[ 𝓓 ] (F ₁ f))
(F -∘) g f = Functor.comp F g f

_∘-func_ :
  {i j k l m n : ULevel}
  {𝓒 : Precategory {i} {j}}
  {𝓓 : Precategory {k} {l}}
  {𝓔 : Precategory {m} {n}}
  → 𝓓 ⇒ 𝓔
  → 𝓒 ⇒ 𝓓
  → 𝓒 ⇒ 𝓔
G ∘-func F = admit _
