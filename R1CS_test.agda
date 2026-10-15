{-# OPTIONS --cubical-compatible #-}

module r1cs where

open import Data.Nat
open import Data.Vec
open import Data.Product
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality


{- xy + 8 . xy = z - 8 -}

postulate
  𝔽 : Set
  _𝔽+_ :  𝔽 →  𝔽 →  𝔽
  _𝔽*_ :  𝔽 →  𝔽 →  𝔽
  𝔽∅ : 𝔽

DotProduct : {n : ℕ} → Vec 𝔽 n → Vec 𝔽 n → 𝔽
DotProduct [] [] = 𝔽∅
DotProduct (x ∷ Lisx) (y ∷ Lisy) = (x 𝔽* y) 𝔽+ (DotProduct Lisx Lisy)

record Constraint (n : ℕ) : Set where
  rowa : Vec 𝔽 n
  rowb : Vec 𝔽 n
  rowc : Vec 𝔽 n

Satisfies : {n : ℕ} → (Vec 𝔽 n) → Constraint n → Set
Satisfies W C =
  let open Constraint in
  (DotProduct rowa W) 𝔽* (DotProduct rowb  W) ≡ (DotProduct rowc W)

R1cs : {m n : ℕ} → Set
R1cs m n = Vec (Constraint n) m

data SysSas {m n : ℕ} (W : Vec 𝔽 n) : R1cs m n → Set where
  all-sastified : {Sys : R1cs m n}
    → ((c : Constraint) → (c Sys) → Satisfies W c)
    → SysSas W Sys
  

x : ℕ
x = zero

y : ℕ
y = suc zero

