{-# OPTIONS --without-K #-}

open import Lib
open import Category.AKS

module Quotient.Ordinary.Core {i j} (𝓒 : Precategory {i} {j}) (F : 𝓒 ⇒ 𝓒) where
  open Functor F renaming (obj to F₀ ; hom to F₁)

  -- TODO: set operator precedence
  _∘_ = Precategory.comp 𝓒

  alg-struct : / 𝓒 / → Type j
  alg-struct X = 𝓒 [ F₀ X , X ]

  is-alg-hom : {X Y : / 𝓒 /} (θ : alg-struct X) (ρ : alg-struct Y) → 𝓒 [ X , Y ] → Type j
  is-alg-hom θ ρ f = (f ∘ θ) == (ρ ∘ F₁ f)

  record Alg₀ : Type (i ⊔ j) where
    constructor alg

    field
      X : / 𝓒 /
      θ : alg-struct X

  record Alg₁ (𝓧 𝓨 : Alg₀) : Type j where
    constructor alg-hom

    open Alg₀ 𝓧
    open Alg₀ 𝓨 renaming (X to Y ; θ to ρ)

    field
      f : 𝓒 [ X , Y ]
      f₀ : is-alg-hom θ ρ f

  alg-hom= : {𝓧 𝓨 : Alg₀} (𝓯 𝓰 : Alg₁ 𝓧 𝓨) → Alg₁.f 𝓯 == Alg₁.f 𝓰 → 𝓯 == 𝓰
  alg-hom= {alg X θ} {alg Y ρ} (alg-hom f f₀) (alg-hom .f g₀) refl = ap (alg-hom f) (Precategory.hom-set 𝓒 (F₀ X) Y _ _ f₀ g₀)

  -- TODO: Show that hom-set property of 𝓒 carries over to F-alg
  Alg-hom-set : (x y : Alg₀) → uip (Alg₁ x y)
  Alg-hom-set 𝓧 𝓨 𝓯 𝓰 p q = admit _

  -- TODO: Add equational proof that this works out
  Alg-id : (𝓧 : Alg₀) → Alg₁ 𝓧 𝓧
  Alg-id (alg X θ) = alg-hom (𝟙 𝓒 X) (admit _)

  -- TODO: Add equational proof that this works out
  Alg-comp :
    {𝓧 𝓨 𝓩 : Alg₀}
    (g : Alg₁ 𝓨 𝓩)
    (f : Alg₁ 𝓧 𝓨)
    → Alg₁ 𝓧 𝓩
  Alg-comp {alg X θ} {alg Y ρ} {alg Z ζ} (alg-hom g g₀) (alg-hom f f₀) = alg-hom (g ∘ f) (admit _)

  _∘[alg]_ = Alg-comp

  Alg-comp-left-id :
    {𝓧 𝓨 : Alg₀}
    (𝓯 : Alg₁ 𝓧 𝓨)
    → (Alg-id 𝓨 ∘[alg] 𝓯) == 𝓯
  Alg-comp-left-id {𝓧} {𝓨} 𝓯 =
    alg-hom=
      (Alg-id 𝓨 ∘[alg] 𝓯)
      𝓯
      (Precategory.comp-left-id 𝓒 (Alg₁.f 𝓯))

  Alg-comp-right-id :
    {𝓧 𝓨 : Alg₀}
    (𝓯 : Alg₁ 𝓧 𝓨)
    → (𝓯 ∘[alg] Alg-id 𝓧) == 𝓯
  Alg-comp-right-id {𝓧} {𝓨} 𝓯 =
    alg-hom=
      (𝓯 ∘[alg] Alg-id 𝓧)
      𝓯
      (Precategory.comp-right-id 𝓒 (Alg₁.f 𝓯))

  Alg-comp-assoc :
    {𝓧 𝓨 𝓩 𝓦 : Alg₀}
    (h : Alg₁ 𝓩 𝓦)
    (g : Alg₁ 𝓨 𝓩)
    (f : Alg₁ 𝓧 𝓨)
    → ((h ∘[alg] g) ∘[alg] f) == (h ∘[alg] (g ∘[alg] f))
  Alg-comp-assoc 𝓱 𝓰 𝓯 =
    alg-hom=
      ((𝓱 ∘[alg] 𝓰) ∘[alg] 𝓯)
      (𝓱 ∘[alg] (𝓰 ∘[alg] 𝓯))
      (Precategory.comp-assoc 𝓒 (Alg₁.f 𝓱) (Alg₁.f 𝓰) (Alg₁.f 𝓯))

  Alg : Precategory {i ⊔ j} {j}
  Alg = record
          { obj = Alg₀
          ; hom = Alg₁
          ; hom-set = Alg-hom-set
          ; id = Alg-id
          ; comp = Alg-comp
          ; comp-left-id = Alg-comp-left-id
          ; comp-right-id = Alg-comp-right-id
          ; comp-assoc = Alg-comp-assoc
          }
