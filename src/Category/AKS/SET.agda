{-# OPTIONS --without-K #-}

module Category.AKS.SET where

open import Lib
open import Category.AKS.Core

SET : Precategory
SET = record
        { obj = Σ Type₀ uip
        ; hom = λ { (x , p) (y , q) → x → y }
        ; hom-set = λ { (x , p) (y , q) f g → uip→ x y q f g }
        ; id = λ { (x , _) z → z }
        ; comp = λ { g f x → g (f x) }
        ; comp-left-id = λ f → refl
        ; comp-right-id = λ f → refl
        ; comp-assoc = λ h g f → refl
        }

open import Category.AKS.Limits.Product

-- TODO: Do universal property of products in Set
SET-has-products : has-products SET
SET-has-products (A , p) (B , q) = (((A × B) , admit _) , cone fst snd) , admit _
