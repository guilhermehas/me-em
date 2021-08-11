{-# OPTIONS --guardedness --sized-types --overlapping-instances #-}
module Properties where

open import Data.Nat
open import Function
open import Data.Product hiding (_<*>_)
open import Data.List.Relation.Unary.Any hiding (any)
open import Data.Vec as V
open import Codata.Stream as S
open import Data.Bool

open import HDec
open import Generators


Property : Set → Set
Property P = (depth : ℕ) → HDec P

record IsProp (t : Set → Set) : Set₁ where
  constructor is-prop
  field toProp : (∀{p} → t p → Property p)

instance
  IsSearchIsProp : ∀{S} → ⦃ P : IsSearch S ⦄ → IsProp S
  IsSearchIsProp = is-prop (const ∘ toHDec)
  PropertyIsProp = is-prop id


open IsProp ⦃ ... ⦄

PropType : ∀{P} → ℕ → Property P → Set
PropType d p = HDecType (p d)

check : ∀{P} → (d : ℕ) → (p : Property P) → PropType d p
check d p = evidence (p d)

exists : ∀ {X}{p : X → Set}{prop}
       → ⦃ g : Gen X  ⦄
       → ⦃ P : IsProp prop ⦄
       → ((x : X) → prop (p x))
       → Property (∃ p)
exists {p = p} {prop} ⦃ s ⦄ f d
   = let xs = V.toList $ S.take d s
      in (| weaken (any xs λ x → toProp (f x) d)|)
  where
    weaken : ∀{ls} → Any p ls → ∃ p
    weaken (here   x) = _ , x
    weaken (there  y) = weaken y
