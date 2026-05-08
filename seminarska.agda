module seminarska where

open import Data.Nat
open import Data.Empty

-- (1)

data Formula : Set where 
  Var : ℕ → Formula
  ¬_ : Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula

infixr 6 _∧_
infixr 5 _∨_
infix 7 ¬_

-- Primeri formul
_ : Formula
_ = Var 0 ∧ ¬ Var 1

_ : Formula
_ = Var 0 ∨ Var 1 ∧ Var 2 ∧ Var 4

-- (2)

data Literal : Set where
  Var : ℕ → Literal
  ¬Var : ℕ → Literal

data NNF : Set where
  Lit : Literal → NNF
  _∧_ : NNF → NNF → NNF
  _∨_ : NNF → NNF → NNF

-- Primeri NNF formul
_ : NNF
_ = Lit (Var 0) ∧ Lit (¬Var 1)      -- x₀ ∧ ¬x₁

_ : NNF
_ = (Lit (Var 0) ∨ Lit (¬Var 1)) ∧ Lit (Var 2)


-- (3)
-- funkcija to nnf
-- tip
to-nnf : Formula → NNF

to-nnf (Var n)   = Lit (Var n)
to-nnf (φ ∧ ψ)   = to-nnf φ ∧ to-nnf ψ
to-nnf (φ ∨ ψ)   = to-nnf φ ∨ to-nnf ψ
to-nnf (¬ (Var n)) = Lit (¬Var n)
to-nnf (¬ (φ ∧ ψ)) = to-nnf (¬ φ) ∨ to-nnf (¬ ψ)
to-nnf (¬ (φ ∨ ψ)) = to-nnf (¬ φ) ∧ to-nnf (¬ ψ)
to-nnf (¬ (¬ φ))   = to-nnf φ


-- (4)