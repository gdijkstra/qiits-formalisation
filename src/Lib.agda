{-# OPTIONS --without-K #-}

module Lib where

open import Agda.Primitive public using (lzero ; _⊔_)
  renaming (Level to ULevel; lsuc to lsucc)

Type : (i : ULevel) → Set (lsucc i)
Type i = Set i

Type₀ = Type lzero
Type0 = Type lzero

Type₁ = Type (lsucc lzero)
Type1 = Type (lsucc lzero)

postulate
  admit : {i : ULevel} (A : Type i) → A

infix 30 _==_

data _==_ {i} {A : Type i} (a : A) : A → Type i where
  refl : a == a

Id : {i : ULevel} (A : Type i) → A → A → Type i
Id A x y = (x == y)

ap : {i j : ULevel} {A : Type i} {B : Type j}
  (f : A → B)
  {x y : A}
  (p : x == y)
  → f x == f y
ap f refl = refl

sym : {i : ULevel} {A : Type i} {x y : A}
  → x == y → y == x
sym refl = refl

transport :
  ∀ {i j}
  {A : Type i} (B : A → Type j)
  {x y : A} (p : x == y)
  → B x → B y
transport B refl x = x

uip : {i : ULevel} (A : Type i) → Type i
uip A = (x y : A) (p q : x == y) → p == q

-- TODO: This requires function extensionality
uip→ : {i j : ULevel} (A : Type i) (B : Type j) → uip B → uip (A → B)
uip→ A B p = λ f g s t → admit _

infixr 60 _,_

record Σ {i j} (A : Type i) (B : A → Type j) : Type (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

_×_ : {i j : ULevel} → (A : Type i) (B : Type j) → Type (i ⊔ j)
A × B = Σ A (λ _ → B)
