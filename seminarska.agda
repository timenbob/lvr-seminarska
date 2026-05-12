module seminarska where

open import Data.Nat
open import Data.Empty

open import Data.List    using (List; []; _∷_)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool    using (Bool; not; true; false) renaming (_∧_ to _∧ᵇ_; _∨_ to _∨ᵇ_)
open import Relation.Binary using (DecidableEquality)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (⊤; tt)
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
record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)

open DecType

module Assoc (K : DecType) (V : Set) where

  Assoc : Set
  Assoc = List (carr K × V)  

  _∈_ : carr K → Assoc → Set
  k ∈ [] = ⊥
  k ∈ ((k' , v) ∷ kvs) with test-≡ K k k'
  ... | yes _ = ⊤
  ... | no  _ = k ∈ kvs
  
  lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
  lookup {k = k} {[]} ()
  lookup {k = k} {(k' , v) ∷ kvs} p with test-≡ K k k'
  ... | yes _ = v
  ... | no  _ = lookup {k = k} {kvs = kvs} p

  _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? [] = no (λ ())
  k ∈? ((k' , v) ∷ kvs) with test-≡ K k k'
  ... | yes _ = yes tt
  ... | no  _ = k ∈? kvs

  _‼_ : (kvs : Assoc) → (k : carr K) → Maybe V
  [] ‼ k = nothing
  ((k' , v) ∷ kvs) ‼ k with test-≡ K k k'
  ... | yes _ = just v
  ... | no  _ = kvs ‼ k

  _[_]≔_ : Assoc → carr K → V → Assoc
  [] [ k ]≔ v = (k , v) ∷ []
  ((k' , v') ∷ kvs) [ k ]≔ v with test-≡ K k k'
  ... | yes _ = (k , v) ∷ kvs  
  ... | no  _ = (k' , v') ∷ (kvs [ k ]≔ v) 


-- (5)
VarDec : DecType
VarDec = record { carr = ℕ ; test-≡ = _≟_ }

open Assoc VarDec Bool renaming (Assoc to Assignment)

eval : Assignment → Formula → Maybe Bool
eval ρ (Var n) = ρ ‼ n
eval ρ (¬ φ) with eval ρ φ
... | just b  = just (not b)
... | nothing = nothing
eval ρ (φ ∧ ψ) with eval ρ φ | eval ρ ψ
... | just b₁ | just b₂ = just (b₁ ∧ᵇ b₂)
... | _       | _       = nothing
eval ρ (φ ∨ ψ) with eval ρ φ | eval ρ ψ
... | just b₁ | just b₂ = just (b₁ ∨ᵇ b₂)
... | _       | _       = nothing

-- Primeri
ρ₅ : Assignment
ρ₅ = (0 , true) ∷ (1 , false) ∷ []

_ : eval ρ₅ (Var 0) ≡ just true
_ = refl

_ : eval ρ₅ (Var 0 ∧ Var 1) ≡ just false
_ = refl

_ : eval ρ₅ (Var 0 ∨ Var 1) ≡ just true
_ = refl

_ : eval ρ₅ (Var 2) ≡ nothing
_ = refl

-- (6)
eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf ρ (Lit (Var n)) = ρ ‼ n
eval-nnf ρ (Lit (¬Var n)) with ρ ‼ n
... | just b  = just (not b)
... | nothing = nothing
eval-nnf ρ (φ ∧ ψ) with eval-nnf ρ φ | eval-nnf ρ ψ
... | just b₁ | just b₂ = just (b₁ ∧ᵇ b₂)
... | _       | _       = nothing
eval-nnf ρ (φ ∨ ψ) with eval-nnf ρ φ | eval-nnf ρ ψ
... | just b₁ | just b₂ = just (b₁ ∨ᵇ b₂)
... | _       | _       = nothing

-- Primeri za eval-nnf
ρ₆ : Assignment
ρ₆ = (0 , true) ∷ (1 , false) ∷ []
_ : eval-nnf ρ₆ (Lit (Var 0)) ≡ just true
_ = refl

_ : eval-nnf ρ₆ (Lit (¬Var 1)) ≡ just true
_ = refl

_ : eval-nnf ρ₆ (Lit (Var 0) ∧ Lit (Var 1)) ≡ just false
_ = refl

_ : eval-nnf ρ₆ (Lit (Var 0) ∨ Lit (Var 2)) ≡ nothing
_ = refl

_ : eval-nnf ρ₆ ((Lit (Var 0) ∨ Lit (Var 1)) ∧ Lit (¬Var 1)) ≡ just true
_ = refl

-- (7) CNF type
data Disjunct : Set where
  Lit : Literal → Disjunct
  _∨_ : Literal → Disjunct → Disjunct

data CNF : Set where
  Dis : Disjunct → CNF
  _∧_ : Disjunct → CNF → CNF

-- Primeri CNF formul
-- x₀
_ : CNF
_ = Dis (Lit (Var 0))

-- (x₀ ∨ ¬x₁)
_ : CNF
_ = Dis (Var 0 ∨ Lit (¬Var 1))

-- (x₀ ∨ ¬x₁) ∧ (x₂)
_ : CNF
_ = (Var 0 ∨ Lit (¬Var 1)) ∧ Dis (Lit (Var 2))
