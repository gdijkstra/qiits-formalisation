{-# OPTIONS --without-K #-}

module Category.Untruncated.Core where

open import Lib

record Precategory {i j} : Type (lsucc (i ⊔ j)) where
  field
    obj : Type i
    hom : obj → obj → Type j
    id : (x : obj) → hom x x
    comp : {x y z : obj} → hom y z → hom x y → hom x z
    comp-left-id : {x y : obj} (f : hom x y) → comp (id y) f == f
    comp-right-id : {x y : obj} (f : hom x y) → comp f (id x) == f
    comp-assoc : {x y z w : obj} (h : hom z w) (g : hom y z) (f : hom x y)
               → comp (comp h g) f == comp h (comp g f)

/_/ : {i j : ULevel} → Precategory {i} {j} → Type i
/ 𝓒 / = Precategory.obj 𝓒

_[_,_] : {i j : ULevel} (𝓒 : Precategory {i} {j}) → / 𝓒 / → / 𝓒 / → Type j
𝓒 [ x , y ] = Precategory.hom 𝓒 x y

TYPE : Precategory
TYPE = record
        { obj = Type₀
        ; hom = λ x y → x → y
        ; id = λ { x z → z }
        ; comp = λ { g f x → g (f x) }
        ; comp-left-id = λ f → refl
        ; comp-right-id = λ f → refl
        ; comp-assoc = λ h g f → refl
        }

Fam : Precategory
Fam = record
        { obj = Σ Type₀ (λ A → A → Type₀)
        ; hom = λ { (A , B) (C , D) → Σ (A → C) (λ f → (x : A) → B x → D (f x)) }
        ; id = λ { (A , B) → (λ x → x) , (λ x z → z) }
        ; comp = λ { (f , g) (h , i) → (λ z → f (h z)) , (λ x z → g (h x) (i x z)) }
        ; comp-left-id = λ f → refl
        ; comp-right-id = λ f → refl
        ; comp-assoc = λ h g f → refl
        }

-- TODO: Category stuff

comp-fun : {i j : ULevel} (𝓒 : Precategory {i} {j}) {x y z : / 𝓒 /} → 𝓒 [ y , z ] → 𝓒 [ x , y ] → 𝓒 [ x , z ]
comp-fun = Precategory.comp

syntax comp-fun 𝓒 g f = g ∘[ 𝓒 ] f

Id : {i j : ULevel} (𝓒 : Precategory {i} {j}) (x : / 𝓒 /) → 𝓒 [ x , x ]
Id 𝓒 x = Precategory.id 𝓒 x

𝟙 : {i j : ULevel} → Precategory {i} {j}
𝟙 {i} {j} = record
      { obj = Unit {i}
      ; hom = λ x y → Unit {j}
      ; id = λ _ → tt
      ; comp = λ _ _ → tt
      ; comp-left-id = λ { tt → refl }
      ; comp-right-id = λ { tt → refl }
      ; comp-assoc = λ h g f → refl
      }
