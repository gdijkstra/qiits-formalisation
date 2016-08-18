{-# OPTIONS --without-K #-}

module Quotient.Sorts.Core where

open import Lib
open import Category.Untruncated
open import Category.Untruncated.Functor

extend :
  (𝓒 : Precategory {lsucc lzero} {lsucc lzero})
  (R : 𝓒 ⇒ TYPE)
  → Precategory {lsucc lzero} {lsucc lzero}
extend 𝓒 R = record
                 { obj = Σ / 𝓒 / (λ X → R ₀ X → Type₀)
                 ; hom = λ { (X , P) (Y , Q) → Σ (𝓒 [ X , Y ]) (λ f → (x : R ₀ X) → P x → Q ((R ₁ f) x)) }
                 ; id = λ { (X , P) → (Id 𝓒 X) , (λ x y → transport P (sym (ap (λ h → h x) (R -id X))) y) }
                 ; comp = λ { (g , g') (f , f') → ((g ∘[ 𝓒 ] f) , (λ x y → admit _)) }
                 ; comp-left-id = λ { (f , f') → admit _ }
                 ; comp-right-id = λ { (f , f') → admit _ }
                 ; comp-assoc = λ { (h , h') (g , g') (f , f') → admit _ }
                 }

data Sorts : Set₁
⟦_⟧ : Sorts → Precategory

data Sorts where
  nil : Sorts
  snoc : (s : Sorts) → ⟦ s ⟧ ⇒ TYPE → Sorts

⟦ nil ⟧ = 𝟙 {lsucc lzero} {lsucc lzero}
⟦ snoc s R ⟧ = extend ⟦ s ⟧ R

t : (s : Sorts) (R : ⟦ s ⟧ ⇒ TYPE) → ⟦ snoc s R ⟧ ⇒ ⟦ s ⟧
t s R = record { obj = λ { (X , P) → X }
               ; hom = λ { (f , f') → f }
               ; id = refl
               ; comp = λ g f → refl
               }

data _∈_ : (𝓒 : Precategory {lsucc lzero} {lsucc lzero}) → Sorts → Type (lsucc (lsucc lzero)) where
  here : (s : Sorts) (R : ⟦ s ⟧ ⇒ TYPE) → ⟦ snoc s R ⟧ ∈ snoc s R
  there : (𝓒 : Precategory) → (s : Sorts) (R : ⟦ s ⟧ ⇒ TYPE) → 𝓒 ∈ s → 𝓒 ∈ snoc s R

U-bar :
  {𝓒 𝓓 : Precategory}
  (s : Sorts)
  (U : 𝓒 ⇒ ⟦ s ⟧)
  (p : 𝓓 ∈ s)
  → 𝓒 ⇒ 𝓓
U-bar .(snoc s R) U (here s R) = U
U-bar .(snoc s R) U (there 𝓓 s R p) = U-bar s (t s R ∘-func U) p

-- Examples
R₀ : ⟦ nil ⟧ ⇒ TYPE
R₀ = record { obj = λ x → Unit ; hom = λ x₁ x₂ → x₂ ; id = refl ; comp = λ g f → refl }

-- ⟦ snoc nil R₀ ⟧ is equivalent to Type
R₁ : ⟦ snoc nil R₀ ⟧ ⇒ TYPE
R₁ = record { obj = λ { (_ , A) → A tt × A tt } ; hom = λ { {_ , A} {_ , B} (_ , f) (x , y) → f tt x , f tt y } ; id = refl ; comp = λ g f → admit _ }

[] : Sorts
[] = nil

[R₀] : Sorts
[R₀] = snoc [] R₀

[R₀,R₁] : Sorts
[R₀,R₁] = snoc [R₀] R₁

test₀ : ⟦ [R₀] ⟧ ∈ [R₀,R₁]
test₀ = there ⟦ [R₀] ⟧ [R₀] R₁ (here [] R₀)

test₁ : (𝓒 : Precategory) → 𝓒 ∈ [R₀,R₁] → 𝓒 == ⟦ [R₀] ⟧ + 𝓒 == ⟦ [R₀,R₁] ⟧
test₁ ._ (here ._ ._) = inr refl
test₁ ._ (there ._ ._ ._ (here .nil ._)) = inl refl
test₁ 𝓒 (there .𝓒 ._ ._ (there .𝓒 .nil ._ ()))
