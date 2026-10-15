{-# OPTIONS --large-indices #-}
open import Data.Nat renaming (_+_ to _N+_; _*_ to _N*_)
open import Data.Vec
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.Reasoning.Setoid
open import Relation.Binary.PropositionalEquality
open import Algebra.Structures
open import Algebra.Bundles using (Ring) 
open import Level using (Level)
open import Algebra.Solver.Ring.Simple

module IntepretadorR1CS {a l} (R : Ring a l) where
  open Ring R using (Carrier; _+_; _*_; 0#; 1#; -_; _≈_; +-identity; *-identity; +-cong; *-cong; distrib)
    renaming (zero to Ring_zero)
  open Algebra.Structures.IsAbelianGroup (Ring.+-isAbelianGroup R) using ()
    renaming (assoc to +-assoc; comm to +-comm; inverse to +-inverse)
  open  Algebra.Solver.Ring.Simple using (solve; _:=_; con; _:+_; _:-_; _:*_)
  
  ≈-sym = Ring.sym R
  ≈-trans = Ring.trans R
  ≈-refl = Ring.refl R
  
  Vector : ℕ → Set a
  Vector n = Vec Carrier n

  Mat : ℕ → ℕ → Set a
  Mat n m = Vec ( Vector n ) m

  P0 : {A : Carrier} → 0# * A ≈ 0#
  P0 {A} = proj₁ Ring_zero A

  0P : {A : Carrier} → A * 0#  ≈ 0#
  0P {A} = proj₂ Ring_zero A

  idA : {A : Carrier} → 1# * A  ≈ A
  idA {A} =  proj₁ *-identity A

  Aid : {A : Carrier} → A * 1# ≈ A
  Aid {A} =  proj₂ *-identity A

  0+ : {A : Carrier} → 0# + A ≈ A
  0+ {A} = proj₁ +-identity A

  +0 : {A : Carrier} → A + 0# ≈ A
  +0 {A} = proj₂ +-identity A

  DotProduct : {n : ℕ} → Vector n → Vector n → Carrier
  DotProduct [] [] = 0#
  DotProduct (x ∷ Lisx) (y ∷ Lisy) = (x * y) + DotProduct Lisx Lisy
  
  CheckCons : {n : ℕ} → Vector n → Vector n → Vector n → Vector n → Set l
  CheckCons A B C witness = (DotProduct A witness) * (DotProduct B witness) ≈ (DotProduct C witness)
  
  data SatisfyAll : {n m : ℕ} →  Mat n m → Mat n m → Mat n m → Vector n → Set l where
      null : {n : ℕ} → {witness : Vector n} → SatisfyAll [] [] [] witness
      cons : {n m : ℕ} → {As Bs Cs : Mat n m} → {A B C witness : Vector n}
        → CheckCons A B C witness
        → SatisfyAll As Bs Cs witness
        → SatisfyAll (A ∷ As) (B ∷ Bs) (C ∷ Cs) witness
        
  Interpreta : {n m : ℕ} →  Mat n m → Mat n m → Mat n m → Vector n → Set l
  Interpreta A B C v = SatisfyAll A B C v

  {- xy + 8 : xy = z-8 -}
  
  x : Carrier
  x = 1# + 1#

  y : Carrier
  y = (1# + 1#) * (1# + 1#)

  z : Carrier
  z = (x * y) + ((1# + 1# + 1# + 1#) * (1# + 1#))

  wit : Vector 4
  wit = 1# ∷ x ∷ y ∷ z ∷ []

  ax : Vector 4
  ax = 0# ∷ 1# ∷ 0# ∷ 0# ∷ []

  b : Vector 4
  b = 0# ∷ 0# ∷ 1# ∷ 0# ∷ []

  c : Vector 4
  c = ((1# + 1# + 1# + 1#) * ((- 1#) + (- 1#))) ∷ 0# ∷ 0# ∷ 1# ∷ []

  MatA : Mat 4 1
  MatA = ax ∷ []
  
  MatB : Mat 4 1
  MatB = b ∷ []
  
  MatC : Mat 4 1
  MatC = c ∷ []

  esq : ((((0# * 1#) + ((1# * x) + ((0# * y) + ((0# * z) + 0#)))) *
     ((0# * 1#) + ((0# * x) + ((1# * y) + ((0# * z) + 0#)))))) ≈ (x * y)
  esq = *-cong SimplificaA SimplificaB
    where
      SimplificaA : ((0# * 1#) + ((1# * x) + ((0# * y) + ((0# * z) + 0#)))) ≈ x
      SimplificaA =
        ≈-trans (+-cong P0 (+-cong idA  (+-cong P0  (+-cong P0 (Ring.refl R))))) (
        ≈-trans (+-cong (Ring.refl R) (+-cong (Ring.refl R)  (+-cong (Ring.refl R)  0+))) (
        ≈-trans (+-cong (Ring.refl R) (+-cong (Ring.refl R) +0)) (
        ≈-trans (+-cong (Ring.refl R) +0)
        0+)))
      SimplificaB : ((0# * 1#) + ((0# * x) + ((1# * y) + ((0# * z) + 0#)))) ≈ y
      SimplificaB =
        ≈-trans (+-cong P0 (+-cong P0  (+-cong idA  (+-cong P0 (Ring.refl R))))) (
        ≈-trans (+-cong (Ring.refl R) (+-cong (Ring.refl R) (+-cong (Ring.refl R) +0))) (
        ≈-trans (+-cong (Ring.refl R) (+-cong (Ring.refl R) +0)) (
        ≈-trans (+-cong (Ring.refl R) 0+)
        0+)))
  {- dir :  (x * y) ≈ ((((1# + 1# + 1# + 1#) * ((- 1#) + (- 1#))) * 1#)  +  ((0# * x) + ((0# * y) + ((1# * z) + 0# ))))
  dir = ≈-trans P1 (≈-trans P2 (≈-trans P3 (≈-trans P4 (≈-trans P5 (≈-trans P6 P7)))))
        where
          N : Carrier
          N = (((1# + 1# + 1# + 1#) * ((- 1#) + (- 1#))) * 1#)

          V : Carrier
          V = ((0# * x) + ((0# * y) + ((1# * z) + 0# )))

          P1 : (x * y) ≈ (x * y) + 0#
          P1 = ≈-sym +0

          P2 : (x * y) + 0# ≈ (x * y) + (N + (- N))
          P2 = ( (N + (- N) ≈ 0#)
                 (x * y) + (N + - N) ≈ (x * y) + 0#
                 (x * y) + 0# ≈ ((x * y) + 0#) )


          +-cong ≈-refl cancela
             where
               cancela : 0# ≈ N + (((1# + 1# + 1# + 1#) * (1# + 1#)))
               cancela =
                 ≈-trans (≈-sym (proj₂ Ring_zero (1# + 1# + 1# + 1#))) (
                 ≈-trans (*-cong ≈-refl (≈-sym (proj₁ +-inverse (1# + 1#)))) (
                 ≈-trans (≈-sym (proj₁ distrib (1# + 1# + 1# + 1#) ((- 1#) + (- 1#)) (1# + 1#))) 
                 (*-cong ≈-refl (+-cong (≈-sym (proj₂ *-identity _)) ≈-refl))))

          P3 : (x * y) + (N + (- N)) ≈ N + ((x * y) + (- N))
          P3 = ≈-trans (≈-sym (+-assoc (x * y) N (- N)))
                       (≈-trans (+-cong (+-comm (x * y) N) ≈-refl)
                               (+-assoc N (x * y) (- N)))

          P4 : N + ((x * y) + (- N)) ≈ N + z
          P4 = +-cong ≈-refl ≈-refl 

          P5 : N + z ≈ N + ((1# * z) + 0#)
          P5 = +-cong ≈-refl (≈-trans (≈-sym +0) (≈-sym (+-cong idA ≈-refl)))

          P6 : N + ((1# * z) + 0#) ≈ N + ((0# * y) + ((1# * z) + 0# ))
          P6 = +-cong ≈-refl (≈-trans 0+ (≈-sym (+-cong P0 ≈-refl)))

          P7 : N + ((0# * y) + ((1# * z) + 0# )) ≈ N + V
          P7 = (+-cong ≈-refl (≈-sym (+-cong P0 ≈-refl))) -}

  postulate
      {- esq : ((((0# * 1#) + ((1# * x) + ((0# * y) + ((0# * z) + 0#)))) * ((0# * 1#) + ((0# * x) + ((1# * y) + ((0# * z) + 0#)))))) ≈ (x * y)-}
      dir : (x * y) ≈ ((((1# + 1# + 1# + 1#) * ((- 1#) + (- 1#))) * 1#)  +  ((0# * x) + ((0# * y) + ((1# * z) + 0# ))))
                      
     

  prova : CheckCons ax b c wit
  prova = ≈-trans esq dir 

  Check : Interpreta MatA MatB MatC wit
  Check = cons prova null 
