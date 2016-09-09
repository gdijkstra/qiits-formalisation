{-# OPTIONS --without-K #-}

open import Lib

module Examples.ConTy where

data Con : Set
data Ty : Con → Set

data Con where
  nil : Con
  snoc : (Γ : Con) → Ty Γ → Con

data Ty where
  Π : (Γ : Con) (A : Ty Γ) (B : Ty (snoc Γ A)) → Ty Γ

record ConTyMotives : Set₁ where
  field
    P : Con → Set
    Q : (Γ : Con) → P Γ → Ty Γ → Set

record ConTyMethods (𝓟 : ConTyMotives) : Set where
  open ConTyMotives 𝓟
  field
    m-nil : P nil
    m-snoc : (Γ : Con) (x : P Γ)
           → (A : Ty Γ) (y : Q Γ x A)
           → P (snoc Γ A)
    m-Π : (Γ : Con) (x : P Γ)
          (A : Ty Γ) (y : Q Γ x A)
          (B : Ty (snoc Γ A)) (z : Q (snoc Γ A) (m-snoc Γ x A y) B)
          → Q Γ x (Π Γ A B)

module _ (𝓟 : ConTyMotives) (𝓜 : ConTyMethods 𝓟) where
  open ConTyMotives 𝓟
  open ConTyMethods 𝓜

  ind-Con : (Γ : Con) → P Γ
  ind-Ty : (Γ : Con) (A : Ty Γ) → Q Γ (ind-Con Γ) A

  ind-Con nil = m-nil
  ind-Con (snoc Γ x) = m-snoc Γ (ind-Con Γ) x (ind-Ty Γ x)
  ind-Ty Γ (Π .Γ A B) = m-Π Γ (ind-Con Γ) A (ind-Ty Γ A) B (ind-Ty (snoc Γ A) B)
