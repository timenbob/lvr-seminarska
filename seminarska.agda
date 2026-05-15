module seminarska  where

open import Data.Nat
open import Data.Empty

open import Data.List    using (List; []; _∷_; _++_)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool    using (Bool; not; true; false) renaming (_∧_ to _∧ᵇ_; _∨_ to _∨ᵇ_)
open import Relation.Binary using (DecidableEquality)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Unit using (⊤; tt)

-- za 9
open import Function using (case_of_)
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

-- (8)  eval-cnf

eval-lit : Assignment → Literal → Maybe Bool
eval-lit ρ (Var n) = ρ ‼ n
eval-lit ρ (¬Var n) with ρ ‼ n
... | just b  = just (not b)
... | nothing = nothing

eval-dis : Assignment → Disjunct → Maybe Bool
eval-dis ρ (Lit l) = eval-lit ρ l
eval-dis ρ (l ∨ d) with eval-lit ρ l | eval-dis ρ d
... | just b₁ | just b₂ = just (b₁ ∨ᵇ b₂)
... | _       | _       = nothing

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf ρ (Dis d) = eval-dis ρ d
eval-cnf ρ (d ∧ φ) with eval-dis ρ d | eval-cnf ρ φ
... | just b₁ | just b₂ = just (b₁ ∧ᵇ b₂)
... | _       | _       = nothing

-- Primeri za eval-cnf
ρ₈ : Assignment
ρ₈ = (0 , true) ∷ (1 , false) ∷ (2 , true) ∷ []

-- x₀ (true)
_ : eval-cnf ρ₈ (Dis (Lit (Var 0))) ≡ just true
_ = refl

-- (x₁ ∨ x₂) (false ∨ true = true)
_ : eval-cnf ρ₈ (Dis (Var 1 ∨ Lit (Var 2))) ≡ just true
_ = refl

-- (x₀ ∨ x₁) ∧ x₁ ((true ∨ false) ∧ false = false)
_ : eval-cnf ρ₈ ((Var 0 ∨ Lit (Var 1)) ∧ Dis (Lit (Var 1))) ≡ just false
_ = refl

-- x₀ ∧ ¬x₁ ∧ x₂ (true ∧ true ∧ true = true)
_ : eval-cnf ρ₈ (Lit (Var 0) ∧ (Lit (¬Var 1) ∧ Dis (Lit (Var 2)))) ≡ just true
_ = refl

-- neznana spremenljivka (x₃)
_ : eval-cnf ρ₈ (Dis (Lit (Var 3))) ≡ nothing
_ = refl


-- (9) DPLL SAT SOLVER

-- najprej poberemo vse spremenljivke na kup
vars-lit : Literal → List ℕ
vars-lit (Var n) = n ∷ []
vars-lit (¬Var n) = n ∷ []  

vars-dis : Disjunct → List ℕ
vars-dis (Lit l)  = vars-lit l     
vars-dis (l ∨ d)  = vars-lit l ++ vars-dis d  

vars-cnf : CNF → List ℕ
vars-cnf (Dis d) = vars-dis d
vars-cnf (d ∧ φ) = vars-dis d ++ vars-cnf φ

-- odstranimo duplikate iz seznama spremenljivk
-- preprosta funkcija, ki preveri ali je število že v seznamu
_∈ₙ?_ : ℕ → List ℕ → Bool
n ∈ₙ? []       = false
n ∈ₙ? (m ∷ ms) with n ≟ m
... | yes _ = true
... | no  _ = n ∈ₙ? ms
-- funkcija, ki odstrani duplikate iz seznama
nub : List ℕ → List ℕ
nub []       = []
nub (x ∷ xs) with x ∈ₙ? xs
... | true  = nub xs
... | false = x ∷ nub xs
-- DPLL algoritem

dpll : List ℕ → Assignment → CNF → Maybe Assignment
dpll [] ρ φ with eval-cnf ρ φ
... | just true = just ρ
... | _         = nothing

dpll (n ∷ ns) ρ φ =
  case dpll ns (ρ [ n ]≔ true) φ of λ where
    (just a) → just a
    nothing  → dpll ns (ρ [ n ]≔ false) φ

sat : CNF → Maybe Assignment
sat φ = dpll (nub (vars-cnf φ)) [] φ

-- x₀ ∧ ¬x₀ (unsatisfiable)
_ : sat (Lit (Var 0) ∧ Dis (Lit (¬Var 0))) ≡ nothing
_ = refl

-- x₀ ∨ x₁ (satisfiable) vrnemo obliko  just ((0 , true) ∷ (1 , true) ∷ []) kar pomeni spr 1 je true in spr 2 je true
_ : sat (Dis (Var 0 ∨ Lit (Var 1))) ≡ just ((0 , true) ∷ (1 , true) ∷ [])
_ = refl

-- (10) Tseytin transformation NNF --> CNF