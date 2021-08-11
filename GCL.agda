{-# OPTIONS --guardedness #-}
module GCL(Σ : Set) where

open import Data.Nat
open import Data.Bool hiding (_≟_)
open import Data.List as L hiding (and; map; filter) renaming (boolFilter to filter)
open import Function hiding (_⟶_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit using (tt)
open import Relation.Nullary
open import Data.Product hiding (Σ)

open import HDec
open import ModelChecker

data Guard : Set
infixr 6　_·_
data GCL : Set where
  if_fi  : List Guard → GCL
  _·_    : GCL → GCL → GCL
  doo_od  : List Guard → GCL
  update : (Σ → Σ) → GCL
  skip   : GCL
data Guard where
  _⟶_ : (⦃ σ : Σ ⦄ → Bool) → GCL → Guard

await : ( ⦃ σ : Σ ⦄ → Bool) → GCL
await g = if g ⟶ skip ∷ [] fi


ops : (GCL × Σ) → List (GCL × Σ)
ops (skip     , σ) = []
ops (update u , σ) = [ skip , u σ ]
ops (skip · y , σ) = [ y , σ ]
ops (x · y    , σ) = L.map (λ { (x , σ) → (x · y) , σ}) $ ops (x , σ)
ops (if xs fi , σ) = L.map (λ { (g ⟶ x) → x , σ }) $ filter (λ { (g ⟶ x) → g ⦃ σ ⦄}) xs
ops (doo xs od , σ) with L.map (λ { (g ⟶ x) → (x · doo xs od) , σ}) $
                        filter (λ { (g ⟶ x) → g ⦃ σ ⦄ }) xs
... | [] = [ skip , σ ]
... | ys = ys

⟦_⟧ : GCL → Diagram GCL Σ
⟦ p ⟧ = td ops p
  where prf : {ℓ : GCL}{σ : Σ} → ℓ ≡ skip → ops (ℓ , σ) ≡ []
        prf refl = refl

while : (⦃ σ : Σ ⦄ → Bool) → GCL → GCL
while g x = doo g ⟶ x ∷ [] od

if′_then_else_ : (⦃ σ : Σ ⦄ → Bool) → GCL → GCL → GCL
if′ g then x else y =
    if g     ⟶ x
    ∷  not g ⟶ y
    ∷  []
    fi
skip? : (ℓ : GCL) → Dec (ℓ ≡ skip)
skip? if x fi    = no (λ () )
skip? (σ · σ₁)   = no (λ () )
skip? doo x od    = no (λ () )
skip? (update x) = no (λ () )
skip? skip       = yes refl
