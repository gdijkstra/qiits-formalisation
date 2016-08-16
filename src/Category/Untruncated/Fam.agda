{-# OPTIONS --without-K #-}

module Category.Untruncated.Fam where

open import Lib
open import Category.Untruncated.Core

record FamStructure {i j} (𝓒 : Precategory {i} {j}) : Type (lsucc (i ⊔ j)) where
  field
    fam : / 𝓒 / → Type i
    total : (X : / 𝓒 /) (P : fam X) → / 𝓒 /
    proj : (X : / 𝓒 /) (P : fam X) → 𝓒 [ total X P , X ]
    preimage : (X : / 𝓒 /) (Y : / 𝓒 /) (p : 𝓒 [ Y , X ]) → fam X
    fam-correct₀ : (X : / 𝓒 /) (P : fam X) → preimage X (total X P) (proj X P) == P
    fam-correct₁ : (X Y : / 𝓒 /) (p : 𝓒 [ Y , X ])
      → Id (Σ / 𝓒 / (λ Y' → 𝓒 [ Y' , X ])) (total X (preimage X Y p) , proj X (preimage X Y p)) (Y , p)

Sect : {i j : ULevel} (𝓒 : Precategory {i} {j}) {X Y : / 𝓒 /} → 𝓒 [ X , Y ] → Type j
Sect 𝓒 {X} {Y} p = Σ (𝓒 [ Y , X ]) (λ s → (p ∘[ 𝓒 ] s) == Precategory.id 𝓒 Y)

record DepHomStructure {i j}
  (𝓒 : Precategory {i} {j})
  (fam-structure : FamStructure 𝓒) : Type (lsucc (i ⊔ j)) where
  open FamStructure fam-structure
  field
    DepHom : (X : / 𝓒 /) → fam X → Type j
    graph : (X : / 𝓒 /) (P : fam X) → DepHom X P → Sect 𝓒 (proj X P)
    snd' : (X : / 𝓒 /) (P : fam X) → Sect 𝓒 (proj X P) → DepHom X P
    -- TODO: dephom-correct

TYPE-fam : FamStructure TYPE
TYPE-fam = record
             { fam = λ X → X → Type₀
             ; total = λ X P → Σ X P
             ; proj = λ { X P (x , y) → x }
             ; preimage = λ X Y p x → Σ Y (λ y → p y == x)
             ; fam-correct₀ = admit _
             ; fam-correct₁ = admit _
             }

TYPE-dephom : DepHomStructure TYPE TYPE-fam
TYPE-dephom = record
                { DepHom = λ X P → (x : X) → P x 
                ; graph = λ X P s → (λ a → a , (s a)) , refl
                ; snd' = λ { X P (s , s₀) x → transport P (ap (λ f → f x) s₀) (snd (s x)) }
                }

Fam-fam : FamStructure Fam
Fam-fam = record
            { fam = λ { (A , B) → Σ (A → Type₀) (λ V → (x : A) → B x → V x → Type₀) }
            ; total = λ { (A , B) (V , W) → (Σ A V) , (λ { (x , z) → Σ (B x) (λ y → W x y z) }) }
            ; proj = λ { (A , B) (V , W) → (λ { (x , y) → x }) , (λ { (x , y) (z , w) → z }) }
            ; preimage = λ { (A , B) (C , D) (p , q) → (λ a → Σ C (λ c → p c == a)) , (λ { x y (z , z') → Σ (D  z) (λ w → q z w == transport B (sym z') y ) } ) }
            ; fam-correct₀ = admit _
            ; fam-correct₁ = admit _
            }

Fam-dephom : DepHomStructure Fam Fam-fam
Fam-dephom = record
               { DepHom = λ { (X , P) (V , W) → Σ ((x : X) → V x) (λ f → (x : X) → (y : P x) → W x y (f x)) }
               ; graph = λ { (X , P) (V , W) (f , g) → ((λ x → x , f x) , (λ x y → y , (g x y))) , refl}
               ; snd' = λ { (X , P) (V , W) ((s , t) , s₀) → admit _ }
               }
