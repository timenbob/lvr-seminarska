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

-- obiscna distributivnost
merge-dis : Disjunct → Disjunct → Disjunct
merge-dis (Lit l) d' = l ∨ d'
merge-dis (l ∨ d) d' = l ∨ merge-dis d d'

merge-cnf : CNF → CNF → CNF
merge-cnf (Dis d)  φ = d ∧ φ
merge-cnf (d ∧ ψ)  φ = d ∧ merge-cnf ψ φ

-- a ali (b in c) = (a ali b) in (a ali c)
distri-a-or-cnf : Disjunct → CNF → CNF
distri-a-or-cnf d (Dis d')  = Dis (merge-dis d d')
distri-a-or-cnf d (d' ∧ φ)  = merge-cnf (distri-a-or-cnf d (Dis d')) (distri-a-or-cnf d φ)

disstri-cnf-or-cnf : CNF → CNF → CNF
disstri-cnf-or-cnf (Dis x) y = distri-a-or-cnf x y
disstri-cnf-or-cnf (x ∧ x₁) y = merge-cnf (disstri-cnf-or-cnf (Dis x) y) (disstri-cnf-or-cnf x₁ y) 

to-cnf : NNF → CNF
to-cnf (Lit l) = Dis (Lit l)
to-cnf (φ ∧ ψ) = merge-cnf (to-cnf φ) (to-cnf ψ)
to-cnf (φ ∨ ψ) = disstri-cnf-or-cnf (to-cnf φ) (to-cnf ψ)

-- testi za to-cnf
ρ₁₀ : Assignment
ρ₁₀ = (0 , true) ∷ (1 , false) ∷ (2 , true) ∷ []

-- x₀ → CNF
_ : eval-cnf ρ₁₀ (to-cnf (Lit (Var 0))) ≡ just true
_ = refl

-- x₀ ∧ x₁ → CNF
_ : eval-cnf ρ₁₀ (to-cnf (Lit (Var 0) ∧ Lit (Var 1))) ≡ just false
_ = refl

-- x₀ ∨ x₁ → CNF (distributivnost)
_ : eval-cnf ρ₁₀ (to-cnf (Lit (Var 0) ∨ Lit (Var 1))) ≡ just true
_ = refl

-- (x₀ ∨ x₁) ∧ x₂
_ : eval-cnf ρ₁₀ (to-cnf ((Lit (Var 0) ∨ Lit (Var 1)) ∧ Lit (Var 2))) ≡ just true
_ = refl
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; module ≡-Reasoning)

FunAssignment : Set
FunAssignment = ℕ → Bool

eval-lit-fun : FunAssignment → Literal → Bool
eval-lit-fun ρ (Var n) = ρ n
eval-lit-fun ρ (¬Var n) = not (ρ n)

eval-dis-fun : FunAssignment → Disjunct → Bool
eval-dis-fun ρ (Lit l) = eval-lit-fun ρ l
eval-dis-fun ρ (l ∨ d) = eval-lit-fun ρ l ∨ᵇ eval-dis-fun ρ d

eval-cnf-fun : FunAssignment → CNF → Bool
eval-cnf-fun ρ (Dis d) = eval-dis-fun ρ d
eval-cnf-fun ρ (d ∧ φ) = eval-dis-fun ρ d ∧ᵇ eval-cnf-fun ρ φ

list-to-cnf : Disjunct → List Disjunct → CNF
list-to-cnf d [] = Dis d
list-to-cnf d (x ∷ xs) = d ∧ list-to-cnf x xs

eval-clauses-fun : FunAssignment → List Disjunct → Bool
eval-clauses-fun ρ [] = true
eval-clauses-fun ρ (x ∷ xs) = eval-dis-fun ρ x ∧ᵇ eval-clauses-fun ρ xs

eval-list-to-cnf : ∀ ρ d ds → eval-cnf-fun ρ (list-to-cnf d ds) ≡ eval-dis-fun ρ d ∧ᵇ eval-clauses-fun ρ ds
eval-list-to-cnf ρ d [] = sym (refl-sym)
  where
    refl-sym : eval-dis-fun ρ d ∧ᵇ true ≡ eval-dis-fun ρ d
    refl-sym with eval-dis-fun ρ d
    ... | true = refl
    ... | false = refl
eval-list-to-cnf ρ d (x ∷ xs) = 
  begin
    eval-cnf-fun ρ (d ∧ list-to-cnf x xs)
  ≡⟨ refl ⟩
    eval-dis-fun ρ d ∧ᵇ eval-cnf-fun ρ (list-to-cnf x xs)
  ≡⟨ cong (λ k → eval-dis-fun ρ d ∧ᵇ k) (eval-list-to-cnf ρ x xs) ⟩
    eval-dis-fun ρ d ∧ᵇ (eval-dis-fun ρ x ∧ᵇ eval-clauses-fun ρ xs)
  ≡⟨ refl ⟩
    eval-dis-fun ρ d ∧ᵇ eval-clauses-fun ρ (x ∷ xs)
  ∎
  where
    open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; cong)
    open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
    open ≡-Reasoning

eval-clauses-++ : ∀ ρ xs ys → eval-clauses-fun ρ (xs ++ ys) ≡ eval-clauses-fun ρ xs ∧ᵇ eval-clauses-fun ρ ys
eval-clauses-++ ρ [] ys = sym (refl-true-and)
  where
    refl-true-and : ∀ {b : Bool} → true ∧ᵇ b ≡ b
    refl-true-and {true} = refl
    refl-true-and {false} = refl
eval-clauses-++ ρ (x ∷ xs) ys =
  begin
    eval-clauses-fun ρ ((x ∷ xs) ++ ys)
  ≡⟨ refl ⟩
    eval-dis-fun ρ x ∧ᵇ eval-clauses-fun ρ (xs ++ ys)
  ≡⟨ cong (λ k → eval-dis-fun ρ x ∧ᵇ k) (eval-clauses-++ ρ xs ys) ⟩
    eval-dis-fun ρ x ∧ᵇ (eval-clauses-fun ρ xs ∧ᵇ eval-clauses-fun ρ ys)
  ≡⟨ sym (refl-assoc {eval-dis-fun ρ x} {eval-clauses-fun ρ xs} {eval-clauses-fun ρ ys}) ⟩
    (eval-dis-fun ρ x ∧ᵇ eval-clauses-fun ρ xs) ∧ᵇ eval-clauses-fun ρ ys
  ≡⟨ refl ⟩
    eval-clauses-fun ρ (x ∷ xs) ∧ᵇ eval-clauses-fun ρ ys
  ∎
  where
    open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; cong)
    open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
    open ≡-Reasoning
    
    refl-assoc : ∀ {a b c : Bool} → (a ∧ᵇ b) ∧ᵇ c ≡ a ∧ᵇ (b ∧ᵇ c)
    refl-assoc {true} {true} {true} = refl
    refl-assoc {true} {true} {false} = refl
    refl-assoc {true} {false} {true} = refl
    refl-assoc {true} {false} {false} = refl
    refl-assoc {false} {true} {true} = refl
    refl-assoc {false} {true} {false} = refl
    refl-assoc {false} {false} {true} = refl
    refl-assoc {false} {false} {false} = refl

-- (11) Tseytin transformation NNF --> CNF (Linear size, Equisatisfiable)

neg-lit : Literal → Literal
neg-lit (Var n) = ¬Var n
neg-lit (¬Var n) = Var n

max-lit : Literal → ℕ
max-lit (Var n) = n
max-lit (¬Var n) = n

max-nnf : NNF → ℕ
max-nnf (Lit l) = max-lit l
max-nnf (φ ∧ ψ) = max-nnf φ ⊔ max-nnf ψ
max-nnf (φ ∨ ψ) = max-nnf φ ⊔ max-nnf ψ

-- list-to-cnf is already defined above, but there's a slight difference in what you had.
-- Actually list-to-cnf is already defined locally in phase 3 as:
-- list-to-cnf : Disjunct → List Disjunct → CNF
tseytin-rec : NNF → ℕ → (List Disjunct × Literal × ℕ)
tseytin-rec (Lit l) n = ([] , l , n)
tseytin-rec (φ ∧ ψ) n = 
  let (c1 , l1 , n1) = tseytin-rec φ n
      (c2 , l2 , n2) = tseytin-rec ψ n1
      x = Var n2
      nx = ¬Var n2
      cl1 = nx ∨ Lit l1
      cl2 = nx ∨ Lit l2
      cl3 = x ∨ (neg-lit l1 ∨ Lit (neg-lit l2))
  in (cl1 ∷ cl2 ∷ cl3 ∷ c1 ++ c2 , x , suc n2)
tseytin-rec (φ ∨ ψ) n = 
  let (c1 , l1 , n1) = tseytin-rec φ n
      (c2 , l2 , n2) = tseytin-rec ψ n1
      x = Var n2
      nx = ¬Var n2
      cl1 = x ∨ Lit (neg-lit l1)
      cl2 = x ∨ Lit (neg-lit l2)
      cl3 = nx ∨ (l1 ∨ Lit l2)
  in (cl1 ∷ cl2 ∷ cl3 ∷ c1 ++ c2 , x , suc n2)

tseytin : NNF → CNF
tseytin φ = 
  let (clauses , root , _) = tseytin-rec φ (suc (max-nnf φ))
  in list-to-cnf (Lit root) clauses


eval-nnf-fun : FunAssignment → NNF → Bool
eval-nnf-fun ρ (Lit l) = eval-lit-fun ρ l
eval-nnf-fun ρ (φ ∧ ψ) = eval-nnf-fun ρ φ ∧ᵇ eval-nnf-fun ρ ψ
eval-nnf-fun ρ (φ ∨ ψ) = eval-nnf-fun ρ φ ∨ᵇ eval-nnf-fun ρ ψ

-- Truth table proofs for gates
open import Data.Empty using (⊥-elim)

and-gate-sound : ∀ {a b c : Bool} → 
  (not a ∨ᵇ b) ∧ᵇ (not a ∨ᵇ c) ∧ᵇ (a ∨ᵇ not b ∨ᵇ not c) ≡ true → 
  a ≡ b ∧ᵇ c
and-gate-sound {true} {true} {true} p = refl
and-gate-sound {true} {true} {false} ()
and-gate-sound {true} {false} {true} ()
and-gate-sound {true} {false} {false} ()
and-gate-sound {false} {true} {true} ()
and-gate-sound {false} {true} {false} p = refl
and-gate-sound {false} {false} {true} p = refl
and-gate-sound {false} {false} {false} p = refl

or-gate-sound : ∀ {a b c : Bool} → 
  (a ∨ᵇ not b) ∧ᵇ (a ∨ᵇ not c) ∧ᵇ (not a ∨ᵇ b ∨ᵇ c) ≡ true → 
  a ≡ b ∨ᵇ c
or-gate-sound {true} {true} {true} p = refl
or-gate-sound {true} {true} {false} p = refl
or-gate-sound {true} {false} {true} p = refl
or-gate-sound {true} {false} {false} ()
or-gate-sound {false} {true} {true} ()
or-gate-sound {false} {true} {false} ()
or-gate-sound {false} {false} {true} ()
or-gate-sound {false} {false} {false} p = refl


lemma-extract-and : ∀ {a b c d : Bool} → a ∧ᵇ (b ∧ᵇ (c ∧ᵇ d)) ≡ true → (a ∧ᵇ (b ∧ᵇ c)) ≡ true × d ≡ true
lemma-extract-and {true} {true} {true} {true} p = refl , refl

lemma-split-and : ∀ {a b : Bool} → a ∧ᵇ b ≡ true → a ≡ true × b ≡ true
lemma-split-and {true} {true} p = refl , refl

eval-neg-lit : ∀ ρ l → eval-lit-fun ρ (neg-lit l) ≡ not (eval-lit-fun ρ l)
eval-neg-lit ρ (Var n) = refl
eval-neg-lit ρ (¬Var n) = sym (not-not (ρ n))
  where
    not-not : ∀ b → not (not b) ≡ b
    not-not true = refl
    not-not false = refl

open import Data.Product using (Σ; _×_; _,_)

SatisfiableNNF-Fun : NNF → Set
SatisfiableNNF-Fun φ = Σ FunAssignment (λ ρ → eval-nnf-fun ρ φ ≡ true)

SatisfiableCNF-Fun : CNF → Set
SatisfiableCNF-Fun φ = Σ FunAssignment (λ ρ → eval-cnf-fun ρ φ ≡ true)



-- Phase 3: Soundness Theorem
open import Relation.Binary.PropositionalEquality using (subst; trans)
tseytin-rec-sound : ∀ φ ρ n → 
  eval-clauses-fun ρ (proj₁ (tseytin-rec φ n)) ≡ true → 
  eval-lit-fun ρ (proj₁ (proj₂ (tseytin-rec φ n))) ≡ eval-nnf-fun ρ φ
tseytin-rec-sound (Lit l) ρ n p = refl
tseytin-rec-sound (φ ∧ ψ) ρ n p with tseytin-rec φ n | tseytin-rec-sound φ ρ n
... | (c1 , l1 , n1) | snd-φ with tseytin-rec ψ n1 | tseytin-rec-sound ψ ρ n1
... | (c2 , l2 , n2) | snd-ψ =
  let
    step1 = subst (λ k → (not (ρ n2) ∨ᵇ eval-lit-fun ρ l1) ∧ᵇ ((not (ρ n2) ∨ᵇ eval-lit-fun ρ l2) ∧ᵇ ((ρ n2 ∨ᵇ eval-lit-fun ρ (neg-lit l1) ∨ᵇ k) ∧ᵇ eval-clauses-fun ρ (c1 ++ c2))) ≡ true) (eval-neg-lit ρ l2) p
    p-rewritten = subst (λ k → (not (ρ n2) ∨ᵇ eval-lit-fun ρ l1) ∧ᵇ ((not (ρ n2) ∨ᵇ eval-lit-fun ρ l2) ∧ᵇ ((ρ n2 ∨ᵇ k ∨ᵇ not (eval-lit-fun ρ l2)) ∧ᵇ eval-clauses-fun ρ (c1 ++ c2))) ≡ true) (eval-neg-lit ρ l1) step1
    p-split : ((not (ρ n2) ∨ᵇ eval-lit-fun ρ l1) ∧ᵇ ((not (ρ n2) ∨ᵇ eval-lit-fun ρ l2) ∧ᵇ (ρ n2 ∨ᵇ not (eval-lit-fun ρ l1) ∨ᵇ not (eval-lit-fun ρ l2)))) ≡ true × eval-clauses-fun ρ (c1 ++ c2) ≡ true
    p-split = lemma-extract-and {not (ρ n2) ∨ᵇ eval-lit-fun ρ l1} {not (ρ n2) ∨ᵇ eval-lit-fun ρ l2} {ρ n2 ∨ᵇ not (eval-lit-fun ρ l1) ∨ᵇ not (eval-lit-fun ρ l2)} {eval-clauses-fun ρ (c1 ++ c2)} p-rewritten
    gate-p = proj₁ p-split
    clauses-p = proj₂ p-split
    x-val-eq = and-gate-sound {ρ n2} {eval-lit-fun ρ l1} {eval-lit-fun ρ l2} gate-p
    clauses-split : eval-clauses-fun ρ c1 ≡ true × eval-clauses-fun ρ c2 ≡ true
    clauses-split = lemma-split-and (trans (sym (eval-clauses-++ ρ c1 c2)) clauses-p)
    IH1 = snd-φ (proj₁ clauses-split)
    IH2 = snd-ψ (proj₂ clauses-split)
  in
  begin
    ρ n2
  ≡⟨ x-val-eq ⟩
    eval-lit-fun ρ l1 ∧ᵇ eval-lit-fun ρ l2
  ≡⟨ cong (λ k → k ∧ᵇ eval-lit-fun ρ l2) IH1 ⟩
    eval-nnf-fun ρ φ ∧ᵇ eval-lit-fun ρ l2
  ≡⟨ cong (λ k → eval-nnf-fun ρ φ ∧ᵇ k) IH2 ⟩
    eval-nnf-fun ρ φ ∧ᵇ eval-nnf-fun ρ ψ
  ∎
  where open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning) ; open ≡-Reasoning

tseytin-rec-sound (φ ∨ ψ) ρ n p with tseytin-rec φ n | tseytin-rec-sound φ ρ n
... | (c1 , l1 , n1) | snd-φ with tseytin-rec ψ n1 | tseytin-rec-sound ψ ρ n1
... | (c2 , l2 , n2) | snd-ψ =
  let 
    step1 = subst (λ k → (ρ n2 ∨ᵇ eval-lit-fun ρ (neg-lit l1)) ∧ᵇ ((ρ n2 ∨ᵇ k) ∧ᵇ ((not (ρ n2) ∨ᵇ eval-lit-fun ρ l1 ∨ᵇ eval-lit-fun ρ l2) ∧ᵇ eval-clauses-fun ρ (c1 ++ c2))) ≡ true) (eval-neg-lit ρ l2) p
    p-rewritten = subst (λ k → (ρ n2 ∨ᵇ k) ∧ᵇ ((ρ n2 ∨ᵇ not (eval-lit-fun ρ l2)) ∧ᵇ ((not (ρ n2) ∨ᵇ eval-lit-fun ρ l1 ∨ᵇ eval-lit-fun ρ l2) ∧ᵇ eval-clauses-fun ρ (c1 ++ c2))) ≡ true) (eval-neg-lit ρ l1) step1
    p-split : ((ρ n2 ∨ᵇ not (eval-lit-fun ρ l1)) ∧ᵇ ((ρ n2 ∨ᵇ not (eval-lit-fun ρ l2)) ∧ᵇ (not (ρ n2) ∨ᵇ eval-lit-fun ρ l1 ∨ᵇ eval-lit-fun ρ l2))) ≡ true × eval-clauses-fun ρ (c1 ++ c2) ≡ true
    p-split = lemma-extract-and {ρ n2 ∨ᵇ not (eval-lit-fun ρ l1)} {ρ n2 ∨ᵇ not (eval-lit-fun ρ l2)} {not (ρ n2) ∨ᵇ eval-lit-fun ρ l1 ∨ᵇ eval-lit-fun ρ l2} {eval-clauses-fun ρ (c1 ++ c2)} p-rewritten
    gate-p = proj₁ p-split
    clauses-p = proj₂ p-split
    x-val-eq = or-gate-sound {ρ n2} {eval-lit-fun ρ l1} {eval-lit-fun ρ l2} gate-p
    clauses-split : eval-clauses-fun ρ c1 ≡ true × eval-clauses-fun ρ c2 ≡ true
    clauses-split = lemma-split-and (trans (sym (eval-clauses-++ ρ c1 c2)) clauses-p)
    IH1 = snd-φ (proj₁ clauses-split)
    IH2 = snd-ψ (proj₂ clauses-split)
  in
  begin
    ρ n2
  ≡⟨ x-val-eq ⟩
    eval-lit-fun ρ l1 ∨ᵇ eval-lit-fun ρ l2
  ≡⟨ cong (λ k → k ∨ᵇ eval-lit-fun ρ l2) IH1 ⟩
    eval-nnf-fun ρ φ ∨ᵇ eval-lit-fun ρ l2
  ≡⟨ cong (λ k → eval-nnf-fun ρ φ ∨ᵇ k) IH2 ⟩
    eval-nnf-fun ρ φ ∨ᵇ eval-nnf-fun ρ ψ
  ∎
  where open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning) ; open ≡-Reasoning


tseytin-sound-lemma : ∀ φ ρ → eval-cnf-fun ρ (tseytin φ) ≡ true → eval-nnf-fun ρ φ ≡ true
tseytin-sound-lemma φ ρ p = 
  let
    (clauses , root , n-max) = tseytin-rec φ (suc (max-nnf φ))
    p2 = trans (sym (eval-list-to-cnf ρ (Lit root) clauses)) p
    split-p2 = lemma-split-and p2
    root-p = proj₁ split-p2
    clauses-p = proj₂ split-p2
    root-eq = tseytin-rec-sound φ ρ (suc (max-nnf φ)) clauses-p
  in trans (sym root-eq) root-p
  
tseytin-sound-fun : ∀ φ -> SatisfiableCNF-Fun (tseytin φ) → SatisfiableNNF-Fun φ
tseytin-sound-fun φ (ρ , p) = (ρ , tseytin-sound-lemma φ ρ p)

-- Phase 4: Completeness Theorem


-- Extend an assignment `ρ` by setting index `n` to boolean `b`.
-- `extend-ρ ρ n b` behaves like `ρ` on all indices `x ≠ n`, and
-- returns `b` when queried at `n`.
extend-ρ : FunAssignment → ℕ → Bool → FunAssignment
extend-ρ ρ n b x with x ≟ n
... | yes _ = b
... | no _  = ρ x

open import Data.Nat.Properties using (
  <-irrefl
  ; ≤-refl; ≤-trans
  ; m≤n⇒m≤1+n
  ; <-≤-trans; ≤-<-trans
  ; m⊔n<o⇒m<o; m⊔n<o⇒n<o
  ; ⊔-assoc
  ; ⊔-comm
  ; ⊔-lub
  ; m≤m⊔n; m≤n⊔m
  )
open import Relation.Binary.PropositionalEquality using (cong₂; _≢_)

-- Proof that the extension indeed sets `n` to `b`.
extend-ρ-hit : ∀ ρ n b → extend-ρ ρ n b n ≡ b
extend-ρ-hit ρ n b with n ≟ n
... | yes _ = refl
... | no n≠n = ⊥-elim (n≠n refl)

-- If `x ≠ n` then extending at `n` does not change the value at `x`.
extend-ρ-miss : ∀ ρ n b x → x ≢ n → extend-ρ ρ n b x ≡ ρ x
extend-ρ-miss ρ n b x x≢n with x ≟ n
... | yes x≡n = ⊥-elim (x≢n x≡n)
... | no _ = refl

-- Max-variable bounds for CNF fragments (used to show extensions don't affect earlier clauses)
-- `max-dis` computes the maximum variable index appearing in a
-- disjunct (a literal joined with nested disjuncts via `∨`).
max-dis : Disjunct → ℕ
max-dis (Lit l) = max-lit l
max-dis (l ∨ d) = max-lit l ⊔ max-dis d

-- `max-clauses` computes the maximum variable index used across all
-- disjuncts in a clause list. Used for freshness/bounds reasoning.
max-clauses : List Disjunct → ℕ
max-clauses [] = 0
max-clauses (d ∷ ds) = max-dis d ⊔ max-clauses ds

-- Lemma: `max-clauses` distributes over list append up to `⊔`.
max-clauses-++ : ∀ xs ys → max-clauses (xs ++ ys) ≡ max-clauses xs ⊔ max-clauses ys
max-clauses-++ [] ys = refl
max-clauses-++ (x ∷ xs) ys =
  trans
    (cong (λ k → max-dis x ⊔ k) (max-clauses-++ xs ys))
    (sym (⊔-assoc (max-dis x) (max-clauses xs) (max-clauses ys)))

-- Extract left/right inequalities from a bound on the `⊔`.
⊔<-left : ∀ {a b k} → a ⊔ b < k → a < k
⊔<-left {a} {b} {k} p = m⊔n<o⇒m<o a b p

⊔<-right : ∀ {a b k} → a ⊔ b < k → b < k
⊔<-right {a} {b} {k} p = m⊔n<o⇒n<o a b p

-- Successor distributes over `⊔` definitionally (used for mild
-- rewriting when stepping bounds by one).
suc-⊔ : ∀ a b → suc (a ⊔ b) ≡ suc a ⊔ suc b
suc-⊔ zero b = refl
suc-⊔ (suc a) zero = refl
suc-⊔ (suc a) (suc b) = refl

-- Introduce a bound on `a ⊔ b` from bounds on `a` and `b`.
⊔<-intro : ∀ {a b k} → a < k → b < k → a ⊔ b < k
⊔<-intro {a} {b} {k} a<k b<k =
  subst (λ t → t ≤ k) (sym (suc-⊔ a b)) (⊔-lub a<k b<k)

-- Bounded extensionality: if two assignments agree on all vars < k,
-- then all evaluations whose max variable < k are equal.
-- Bounded extensionality: if two assignments agree on all indices
-- `< k`, then evaluation of literals with `max-lit < k` is identical.
eval-lit-equiv-< : ∀ ρ₁ ρ₂ l k → max-lit l < k → (∀ x → x < k → ρ₁ x ≡ ρ₂ x) → eval-lit-fun ρ₁ l ≡ eval-lit-fun ρ₂ l
eval-lit-equiv-< ρ₁ ρ₂ (Var n) k n<k p = p n n<k
eval-lit-equiv-< ρ₁ ρ₂ (¬Var n) k n<k p = cong not (p n n<k)

-- Same idea for disjuncts: evaluations coincide if variable usage is
-- bounded below `k` and assignments agree on indices `< k`.
eval-dis-equiv-< : ∀ ρ₁ ρ₂ d k → max-dis d < k → (∀ x → x < k → ρ₁ x ≡ ρ₂ x) → eval-dis-fun ρ₁ d ≡ eval-dis-fun ρ₂ d
eval-dis-equiv-< ρ₁ ρ₂ (Lit l) k l<k p = eval-lit-equiv-< ρ₁ ρ₂ l k l<k p
eval-dis-equiv-< ρ₁ ρ₂ (l ∨ d) k ld<k p =
  cong₂ _∨ᵇ_
    (eval-lit-equiv-< ρ₁ ρ₂ l k (⊔<-left ld<k) p)
    (eval-dis-equiv-< ρ₁ ρ₂ d k (⊔<-right ld<k) p)

-- Extension of the same idea to lists of disjuncts (clauses): if all
-- disjuncts are bounded below `k` and assignments agree below `k`, the
-- clause evaluation functions are equal.
eval-clauses-equiv-< : ∀ ρ₁ ρ₂ clauses k → max-clauses clauses < k → (∀ x → x < k → ρ₁ x ≡ ρ₂ x) → eval-clauses-fun ρ₁ clauses ≡ eval-clauses-fun ρ₂ clauses
eval-clauses-equiv-< ρ₁ ρ₂ [] k _ p = refl
eval-clauses-equiv-< ρ₁ ρ₂ (d ∷ ds) k pMax pEq =
  cong₂ _∧ᵇ_
    (eval-dis-equiv-< ρ₁ ρ₂ d k (⊔<-left pMax) pEq)
    (eval-clauses-equiv-< ρ₁ ρ₂ ds k (⊔<-right pMax) pEq)

-- And lifted to NNF formulas: evaluations coincide under the same
-- boundedness and agreement hypotheses.
eval-nnf-equiv-< : ∀ ρ₁ ρ₂ φ k → max-nnf φ < k → (∀ x → x < k → ρ₁ x ≡ ρ₂ x) → eval-nnf-fun ρ₁ φ ≡ eval-nnf-fun ρ₂ φ
eval-nnf-equiv-< ρ₁ ρ₂ (Lit l) k l<k p = eval-lit-equiv-< ρ₁ ρ₂ l k l<k p
eval-nnf-equiv-< ρ₁ ρ₂ (φ ∧ ψ) k pMax pEq =
  cong₂ _∧ᵇ_
    (eval-nnf-equiv-< ρ₁ ρ₂ φ k (⊔<-left pMax) pEq)
    (eval-nnf-equiv-< ρ₁ ρ₂ ψ k (⊔<-right pMax) pEq)
eval-nnf-equiv-< ρ₁ ρ₂ (φ ∨ ψ) k pMax pEq =
  cong₂ _∨ᵇ_
    (eval-nnf-equiv-< ρ₁ ρ₂ φ k (⊔<-left pMax) pEq)
    (eval-nnf-equiv-< ρ₁ ρ₂ ψ k (⊔<-right pMax) pEq)

eval-lit-equiv : ∀ ρ₁ ρ₂ l → (∀ x → ρ₁ x ≡ ρ₂ x) → eval-lit-fun ρ₁ l ≡ eval-lit-fun ρ₂ l
eval-lit-equiv ρ₁ ρ₂ (Var n) p = p n
eval-lit-equiv ρ₁ ρ₂ (¬Var n) p = cong not (p n)

eval-dis-equiv : ∀ ρ₁ ρ₂ d → (∀ x → ρ₁ x ≡ ρ₂ x) → eval-dis-fun ρ₁ d ≡ eval-dis-fun ρ₂ d
eval-dis-equiv ρ₁ ρ₂ (Lit l) p = eval-lit-equiv ρ₁ ρ₂ l p
eval-dis-equiv ρ₁ ρ₂ (l ∨ d) p = cong₂ _∨ᵇ_ (eval-lit-equiv ρ₁ ρ₂ l p) (eval-dis-equiv ρ₁ ρ₂ d p)

eval-clauses-equiv : ∀ ρ₁ ρ₂ clauses → (∀ x → ρ₁ x ≡ ρ₂ x) → eval-clauses-fun ρ₁ clauses ≡ eval-clauses-fun ρ₂ clauses
eval-clauses-equiv ρ₁ ρ₂ [] p = refl
eval-clauses-equiv ρ₁ ρ₂ (d ∷ ds) p = cong₂ _∧ᵇ_ (eval-dis-equiv ρ₁ ρ₂ d p) (eval-clauses-equiv ρ₁ ρ₂ ds p)

-- `extend-ρ` does not affect indices strictly less than the fresh bound
-- `n` (used when we extend at a fresh index to set a gate value).
extend-ρ-preserves : ∀ ρ n b x → x < n → extend-ρ ρ n b x ≡ ρ x
extend-ρ-preserves ρ n b x p with x ≟ n
... | yes refl = ⊥-elim (<-irrefl refl p)
... | no _     = refl

-- Monotonicity + bounds for tseytin-rec outputs (under the usual freshness condition).
tseytin-rec-mono : ∀ φ n → n ≤ proj₂ (proj₂ (tseytin-rec φ n))
tseytin-rec-mono (Lit l) n = ≤-refl
tseytin-rec-mono (φ ∧ ψ) n =
  let
    n1 = proj₂ (proj₂ (tseytin-rec φ n))
    n2 = proj₂ (proj₂ (tseytin-rec ψ n1))
  in
  ≤-trans (tseytin-rec-mono φ n) (≤-trans (tseytin-rec-mono ψ n1) (m≤n⇒m≤1+n ≤-refl))
tseytin-rec-mono (φ ∨ ψ) n =
  let
    n1 = proj₂ (proj₂ (tseytin-rec φ n))
    n2 = proj₂ (proj₂ (tseytin-rec ψ n1))
  in
  ≤-trans (tseytin-rec-mono φ n) (≤-trans (tseytin-rec-mono ψ n1) (m≤n⇒m≤1+n ≤-refl))

-- Negation on literals does not change which variables appear, so the
-- maximum index is unchanged.
max-lit-neg-lit : ∀ l → max-lit (neg-lit l) ≡ max-lit l
max-lit-neg-lit (Var n) = refl
max-lit-neg-lit (¬Var n) = refl

{-
  tseytin-rec-bounds

  Purpose:
    Prove that the CNF fragments and fresh root literal produced by
    `tseytin-rec φ n` only mention variable indices strictly less than
    the returned successor bound. Concretely, for input `n` with
    `max-nnf φ < n`, the function returns a triple `(clauses , rootLit , n')`
    such that every clause in `clauses` has `max-clauses clauses < n'` and
    the root literal satisfies `max-lit rootLit < n'`.

  Proof strategy:
    Structural induction on `φ`.
    - Base (Lit): trivial because no new variables are introduced.
    - Conjunction / Disjunction:
        * Recurse on subformulas producing (c1,l1,n1) and (c2,l2,n2).
        * Use monotonicity (`tseytin-rec-mono`) to relate the intermediate
          bounds (`n1 ≤ n2`) so previously-proven bounds lift to the
          larger successor bound.
        * Compute `suc n2` as the new bound for the assembled clauses;
          prove each clause's `max` is < `suc n2` by combining
          sub-bounds with `⊔<-intro` and reshaping equalities when
          necessary using `subst` and `max-lit-neg-lit`.

    These bounds are used later to show extensions of assignments at
    fresh indices do not affect the evaluation of earlier clauses.
  -}

tseytin-rec-bounds : ∀ φ n → max-nnf φ < n → max-clauses (proj₁ (tseytin-rec φ n)) < proj₂ (proj₂ (tseytin-rec φ n)) × max-lit (proj₁ (proj₂ (tseytin-rec φ n))) < proj₂ (proj₂ (tseytin-rec φ n))
tseytin-rec-bounds (Lit l) n p =
  (≤-<-trans z≤n p , p)
tseytin-rec-bounds (φ ∧ ψ) n pMax =
  let
    (c1 , l1 , n1) = tseytin-rec φ n
    (c1Bound , l1Bound) = tseytin-rec-bounds φ n (⊔<-left pMax)

    pψ<n1 : max-nnf ψ < n1
    pψ<n1 = <-≤-trans (⊔<-right pMax) (tseytin-rec-mono φ n)

    (c2 , l2 , n2) = tseytin-rec ψ n1
    (c2Bound , l2Bound) = tseytin-rec-bounds ψ n1 pψ<n1
  in
  let
    n1≤n2 : n1 ≤ n2
    n1≤n2 = tseytin-rec-mono ψ n1

    l1<n2 : max-lit l1 < n2
    l1<n2 = <-≤-trans l1Bound n1≤n2

    c1<n2 : max-clauses c1 < n2
    c1<n2 = <-≤-trans c1Bound n1≤n2

    c1++c2<n2 : max-clauses (c1 ++ c2) < n2
    c1++c2<n2 =
      subst (λ k → k < n2) (sym (max-clauses-++ c1 c2)) (⊔<-intro c1<n2 c2Bound)

    n2≤sn2 : n2 ≤ suc n2
    n2≤sn2 = m≤n⇒m≤1+n ≤-refl

    l1<sn2 : max-lit l1 < suc n2
    l1<sn2 = <-≤-trans l1<n2 n2≤sn2

    l2<sn2 : max-lit l2 < suc n2
    l2<sn2 = <-≤-trans l2Bound n2≤sn2

    c1++c2<sn2 : max-clauses (c1 ++ c2) < suc n2
    c1++c2<sn2 = <-≤-trans c1++c2<n2 n2≤sn2

    cl1Bound : max-dis (¬Var n2 ∨ Lit l1) < suc n2
    cl1Bound = ⊔<-intro ≤-refl l1<sn2

    cl2Bound : max-dis (¬Var n2 ∨ Lit l2) < suc n2
    cl2Bound = ⊔<-intro ≤-refl l2<sn2

    innerBound : (max-lit (neg-lit l1) ⊔ max-lit (neg-lit l2)) < suc n2
    innerBound =
      subst (λ k → k < suc n2)
        (sym (cong₂ _⊔_ (max-lit-neg-lit l1) (max-lit-neg-lit l2)))
        (⊔<-intro l1<sn2 l2<sn2)

    cl3Bound : max-dis (Var n2 ∨ (neg-lit l1 ∨ Lit (neg-lit l2))) < suc n2
    cl3Bound = ⊔<-intro ≤-refl innerBound

    rest2 : max-clauses ((Var n2 ∨ (neg-lit l1 ∨ Lit (neg-lit l2))) ∷ (c1 ++ c2)) < suc n2
    rest2 = ⊔<-intro cl3Bound c1++c2<sn2

    rest1 : max-clauses ((¬Var n2 ∨ Lit l2) ∷ (Var n2 ∨ (neg-lit l1 ∨ Lit (neg-lit l2))) ∷ (c1 ++ c2)) < suc n2
    rest1 = ⊔<-intro cl2Bound rest2

    allBound : max-clauses ((¬Var n2 ∨ Lit l1) ∷ (¬Var n2 ∨ Lit l2) ∷ (Var n2 ∨ (neg-lit l1 ∨ Lit (neg-lit l2))) ∷ (c1 ++ c2)) < suc n2
    allBound = ⊔<-intro cl1Bound rest1
  in
  (allBound , ≤-refl)

tseytin-rec-bounds (φ ∨ ψ) n pMax =
  let
    (c1 , l1 , n1) = tseytin-rec φ n
    (c1Bound , l1Bound) = tseytin-rec-bounds φ n (⊔<-left pMax)

    pψ<n1 : max-nnf ψ < n1
    pψ<n1 = <-≤-trans (⊔<-right pMax) (tseytin-rec-mono φ n)

    (c2 , l2 , n2) = tseytin-rec ψ n1
    (c2Bound , l2Bound) = tseytin-rec-bounds ψ n1 pψ<n1
  in
  let
    n1≤n2 : n1 ≤ n2
    n1≤n2 = tseytin-rec-mono ψ n1

    l1<n2 : max-lit l1 < n2
    l1<n2 = <-≤-trans l1Bound n1≤n2

    c1<n2 : max-clauses c1 < n2
    c1<n2 = <-≤-trans c1Bound n1≤n2

    c1++c2<n2 : max-clauses (c1 ++ c2) < n2
    c1++c2<n2 = subst (λ k → k < n2) (sym (max-clauses-++ c1 c2)) (⊔<-intro c1<n2 c2Bound)

    n2≤sn2 : n2 ≤ suc n2
    n2≤sn2 = m≤n⇒m≤1+n ≤-refl

    l1<sn2 : max-lit l1 < suc n2
    l1<sn2 = <-≤-trans l1<n2 n2≤sn2

    l2<sn2 : max-lit l2 < suc n2
    l2<sn2 = <-≤-trans l2Bound n2≤sn2

    c1++c2<sn2 : max-clauses (c1 ++ c2) < suc n2
    c1++c2<sn2 = <-≤-trans c1++c2<n2 n2≤sn2

    cl1Bound : max-dis (Var n2 ∨ Lit (neg-lit l1)) < suc n2
    cl1Bound =
      subst (λ k → (n2 ⊔ k) < suc n2) (sym (max-lit-neg-lit l1)) (⊔<-intro ≤-refl l1<sn2)

    cl2Bound : max-dis (Var n2 ∨ Lit (neg-lit l2)) < suc n2
    cl2Bound =
      subst (λ k → (n2 ⊔ k) < suc n2) (sym (max-lit-neg-lit l2)) (⊔<-intro ≤-refl l2<sn2)

    cl3Inner : (max-lit l1 ⊔ max-lit l2) < suc n2
    cl3Inner = ⊔<-intro l1<sn2 l2<sn2

    cl3Bound : max-dis (¬Var n2 ∨ l1 ∨ Lit l2) < suc n2
    cl3Bound = ⊔<-intro ≤-refl cl3Inner

    rest2 : max-clauses ((¬Var n2 ∨ l1 ∨ Lit l2) ∷ (c1 ++ c2)) < suc n2
    rest2 = ⊔<-intro cl3Bound c1++c2<sn2

    rest1 : max-clauses ((Var n2 ∨ Lit (neg-lit l2)) ∷ (¬Var n2 ∨ l1 ∨ Lit l2) ∷ (c1 ++ c2)) < suc n2
    rest1 = ⊔<-intro cl2Bound rest2

    allBound : max-clauses ((Var n2 ∨ Lit (neg-lit l1)) ∷ (Var n2 ∨ Lit (neg-lit l2)) ∷ (¬Var n2 ∨ l1 ∨ Lit l2) ∷ (c1 ++ c2)) < suc n2
    allBound = ⊔<-intro cl1Bound rest1
  in
  (allBound , ≤-refl)

-- Gate completeness (truth tables)
and-true-right : ∀ b → b ∧ᵇ true ≡ b
and-true-right true = refl
and-true-right false = refl

and-gate-complete : ∀ b c → (not (b ∧ᵇ c) ∨ᵇ b) ∧ᵇ (not (b ∧ᵇ c) ∨ᵇ c) ∧ᵇ ((b ∧ᵇ c) ∨ᵇ not b ∨ᵇ not c) ≡ true
and-gate-complete true true = refl
and-gate-complete true false = refl
and-gate-complete false true = refl
and-gate-complete false false = refl

or-gate-complete : ∀ b c → ((b ∨ᵇ c) ∨ᵇ not b) ∧ᵇ ((b ∨ᵇ c) ∨ᵇ not c) ∧ᵇ (not (b ∨ᵇ c) ∨ᵇ b ∨ᵇ c) ≡ true
or-gate-complete true true = refl
or-gate-complete true false = refl
or-gate-complete false true = refl
or-gate-complete false false = refl

{-
  tseytin-rec-complete

  Purpose:
    Given a formula `φ`, an assignment `ρ` and a bound `n` with
    `max-nnf φ < n`, construct an assignment `ρ'` that agrees with `ρ`
    on all variables `< n` and satisfies the CNF produced by
    `tseytin-rec φ n`. Moreover, show that the distinguished root literal
    produced by `tseytin-rec` evaluates to the same truth-value as the
    original `φ` under `ρ`.

  Proof strategy:
    Structural induction on `φ`.
    - Base (Lit): take `ρ' = ρ` and return trivial equalities.
    - Conjunction / Disjunction:
        * Recursively obtain `ρ1` and `ρ2` for subformulas ensuring
          their clause-sets are satisfied and root literals correspond to
          subformula evaluations.
        * Compute `b-val` as the gate's Boolean (conjunction/disjunction)
          of the two root-literal evaluations under `ρ2`.
        * Extend `ρ2` at the fresh index `n2` to set the gate variable to
          `b-val`, producing `ρ3`.
        * Transport previously established truths about clauses and
          literals from `ρ1`/`ρ2` to `ρ3` using the `eval-*-equiv-<`
          lemmas and bounds from `tseytin-rec-bounds`.
        * Prove the gate clauses evaluate to `true` by unfolding the
          evaluation and using the constructed equality `ρ3 n2 ≡ b-val`.
        * Finally assemble `clauses-all`, `root-eq` and `bounds` to
          conclude the existential result for `ρ3`.
-}

tseytin-rec-complete : ∀ φ ρ n → 
  max-nnf φ < n →
  Σ FunAssignment (λ ρ' → 
    eval-clauses-fun ρ' (proj₁ (tseytin-rec φ n)) ≡ true ×
    eval-lit-fun ρ' (proj₁ (proj₂ (tseytin-rec φ n))) ≡ eval-nnf-fun ρ φ ×
    (∀ x → x < n → ρ' x ≡ ρ x))
tseytin-rec-complete (Lit l) ρ n pMax = (ρ , (refl , refl , λ x x<n → refl))
tseytin-rec-complete (φ ∧ ψ) ρ n pMax = 
  let (c1 , l1 , n1) = tseytin-rec φ n
      (c2 , l2 , n2) = tseytin-rec ψ n1
      (ρ1 , (IH-c1 , IH-l1 , IH-ρ1)) = tseytin-rec-complete φ ρ n (⊔<-left pMax)
      pψ<n : max-nnf ψ < n
      pψ<n = ⊔<-right pMax
      pψ<n1 : max-nnf ψ < n1
      pψ<n1 = <-≤-trans pψ<n (tseytin-rec-mono φ n)
      (ρ2 , (IH-c2 , IH-l2 , IH-ρ2)) = tseytin-rec-complete ψ ρ1 n1 pψ<n1
      b-val = eval-lit-fun ρ2 l1 ∧ᵇ eval-lit-fun ρ2 l2
      ρ3 = extend-ρ ρ2 n2 b-val
      -- Transport facts about l1/c1 from ρ1 to ρ2 (ρ2 agrees with ρ1 on vars < n1)
      l1Bound : max-lit l1 < n1
      l1Bound = proj₂ (tseytin-rec-bounds φ n (⊔<-left pMax))
      c1Bound : max-clauses c1 < n1
      c1Bound = proj₁ (tseytin-rec-bounds φ n (⊔<-left pMax))
      l1-ρ2≡ : eval-lit-fun ρ2 l1 ≡ eval-lit-fun ρ1 l1
      l1-ρ2≡ =
        eval-lit-equiv-< ρ2 ρ1 l1 n1 l1Bound (λ x x<n1 → IH-ρ2 x x<n1)
      c1-ρ2≡ : eval-clauses-fun ρ2 c1 ≡ eval-clauses-fun ρ1 c1
      c1-ρ2≡ =
        eval-clauses-equiv-< ρ2 ρ1 c1 n1 c1Bound (λ x x<n1 → IH-ρ2 x x<n1)
      c1-ρ2-true : eval-clauses-fun ρ2 c1 ≡ true
      c1-ρ2-true = trans c1-ρ2≡ IH-c1

      -- Transport facts about c1/c2/l1/l2 from ρ2 to ρ3 (ρ3 agrees with ρ2 on vars < n2)
      pρ3< : ∀ x → x < n2 → ρ3 x ≡ ρ2 x
      pρ3< x x<n2 = extend-ρ-preserves ρ2 n2 b-val x x<n2

      l2Bound : max-lit l2 < n2
      l2Bound = proj₂ (tseytin-rec-bounds ψ n1 pψ<n1)
      c2Bound : max-clauses c2 < n2
      c2Bound = proj₁ (tseytin-rec-bounds ψ n1 pψ<n1)

      l1Bound<n2 : max-lit l1 < n2
      l1Bound<n2 = <-≤-trans l1Bound (tseytin-rec-mono ψ n1)
      c1Bound<n2 : max-clauses c1 < n2
      c1Bound<n2 = <-≤-trans c1Bound (tseytin-rec-mono ψ n1)

      l1-ρ3≡ : eval-lit-fun ρ3 l1 ≡ eval-lit-fun ρ2 l1
      l1-ρ3≡ = eval-lit-equiv-< ρ3 ρ2 l1 n2 l1Bound<n2 pρ3<
      l2-ρ3≡ : eval-lit-fun ρ3 l2 ≡ eval-lit-fun ρ2 l2
      l2-ρ3≡ = eval-lit-equiv-< ρ3 ρ2 l2 n2 l2Bound pρ3<
      c1-ρ3≡ : eval-clauses-fun ρ3 c1 ≡ eval-clauses-fun ρ2 c1
      c1-ρ3≡ = eval-clauses-equiv-< ρ3 ρ2 c1 n2 c1Bound<n2 pρ3<
      c2-ρ3≡ : eval-clauses-fun ρ3 c2 ≡ eval-clauses-fun ρ2 c2
      c2-ρ3≡ = eval-clauses-equiv-< ρ3 ρ2 c2 n2 c2Bound pρ3<

      c1-ρ3-true : eval-clauses-fun ρ3 c1 ≡ true
      c1-ρ3-true = trans c1-ρ3≡ c1-ρ2-true
      c2-ρ3-true : eval-clauses-fun ρ3 c2 ≡ true
      c2-ρ3-true = trans c2-ρ3≡ IH-c2

      -- show c1++c2 is true under ρ3
      clauses-ρ3-true : eval-clauses-fun ρ3 (c1 ++ c2) ≡ true
      clauses-ρ3-true =
        let open ≡-Reasoning in
        begin
          eval-clauses-fun ρ3 (c1 ++ c2)
        ≡⟨ eval-clauses-++ ρ3 c1 c2 ⟩
          eval-clauses-fun ρ3 c1 ∧ᵇ eval-clauses-fun ρ3 c2
        ≡⟨ cong₂ _∧ᵇ_ c1-ρ3-true c2-ρ3-true ⟩
          true ∧ᵇ true
        ≡⟨ refl ⟩
          true
        ∎

      -- Gate clauses become true by construction (x := b ∧ c)
      gate-ρ3-true :
        eval-clauses-fun ρ3 ((¬Var n2 ∨ Lit l1) ∷ (¬Var n2 ∨ Lit l2) ∷ (Var n2 ∨ (neg-lit l1 ∨ Lit (neg-lit l2))) ∷ []) ≡ true
      gate-ρ3-true =
        let
          b = eval-lit-fun ρ3 l1
          c = eval-lit-fun ρ3 l2
          x≡ : ρ3 n2 ≡ b ∧ᵇ c
          x≡ =
            let open ≡-Reasoning in
            begin
              ρ3 n2
            ≡⟨ extend-ρ-hit ρ2 n2 b-val ⟩
              b-val
            ≡⟨ cong₂ _∧ᵇ_ (sym l1-ρ3≡) (sym l2-ρ3≡) ⟩
              (eval-lit-fun ρ3 l1 ∧ᵇ eval-lit-fun ρ3 l2)
            ∎
        in
        let open ≡-Reasoning in
        begin
          eval-clauses-fun ρ3
               ((¬Var n2 ∨ Lit l1) ∷ (¬Var n2 ∨ Lit l2) ∷
                 (Var n2 ∨ (neg-lit l1 ∨ Lit (neg-lit l2))) ∷ [])
        ≡⟨ refl ⟩
          (not (ρ3 n2) ∨ᵇ b)
          ∧ᵇ ((not (ρ3 n2) ∨ᵇ c)
              ∧ᵇ (((ρ3 n2) ∨ᵇ eval-lit-fun ρ3 (neg-lit l1)
                   ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
                  ∧ᵇ true))
        ≡⟨ cong
            (λ x → (not x ∨ᵇ b)
                 ∧ᵇ ((not x ∨ᵇ c)
                     ∧ᵇ ((x ∨ᵇ eval-lit-fun ρ3 (neg-lit l1)
                          ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
                         ∧ᵇ true)))
            x≡ ⟩
          (not (b ∧ᵇ c) ∨ᵇ b)
          ∧ᵇ ((not (b ∧ᵇ c) ∨ᵇ c)
              ∧ᵇ (((b ∧ᵇ c) ∨ᵇ eval-lit-fun ρ3 (neg-lit l1)
                   ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
                  ∧ᵇ true))
        ≡⟨ cong
            (λ u → (not (b ∧ᵇ c) ∨ᵇ b)
                 ∧ᵇ ((not (b ∧ᵇ c) ∨ᵇ c)
                     ∧ᵇ (((b ∧ᵇ c) ∨ᵇ u ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
                         ∧ᵇ true)))
            (eval-neg-lit ρ3 l1) ⟩
          (not (b ∧ᵇ c) ∨ᵇ b)
          ∧ᵇ ((not (b ∧ᵇ c) ∨ᵇ c)
              ∧ᵇ (((b ∧ᵇ c) ∨ᵇ not b ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
                  ∧ᵇ true))
        ≡⟨ cong
            (λ v → (not (b ∧ᵇ c) ∨ᵇ b)
                 ∧ᵇ ((not (b ∧ᵇ c) ∨ᵇ c)
                     ∧ᵇ (((b ∧ᵇ c) ∨ᵇ not b ∨ᵇ v)
                         ∧ᵇ true)))
            (eval-neg-lit ρ3 l2) ⟩
          (not (b ∧ᵇ c) ∨ᵇ b)
          ∧ᵇ ((not (b ∧ᵇ c) ∨ᵇ c)
              ∧ᵇ (((b ∧ᵇ c) ∨ᵇ not b ∨ᵇ not c)
                  ∧ᵇ true))
        ≡⟨ cong
            (λ t → (not (b ∧ᵇ c) ∨ᵇ b)
                 ∧ᵇ ((not (b ∧ᵇ c) ∨ᵇ c) ∧ᵇ t))
            (and-true-right ((b ∧ᵇ c) ∨ᵇ not b ∨ᵇ not c)) ⟩
          (not (b ∧ᵇ c) ∨ᵇ b)
          ∧ᵇ ((not (b ∧ᵇ c) ∨ᵇ c)
              ∧ᵇ ((b ∧ᵇ c) ∨ᵇ not b ∨ᵇ not c))
        ≡⟨ and-gate-complete b c ⟩
          true
        ∎

      -- assemble all clauses for (φ ∧ ψ)
      clauses-all : eval-clauses-fun ρ3 (proj₁ (tseytin-rec (φ ∧ ψ) n)) ≡ true
      clauses-all =
        let head = ((¬Var n2 ∨ Lit l1) ∷ ((¬Var n2 ∨ Lit l2) ∷ ((Var n2 ∨ (neg-lit l1 ∨ Lit (neg-lit l2))) ∷ []))) in
        subst (λ t → t ≡ true) (sym (eval-clauses-++ ρ3 head (c1 ++ c2))) (cong₂ _∧ᵇ_ gate-ρ3-true clauses-ρ3-true)

      -- root literal corresponds to eval-nnf under the original assignment ρ
      root-eq : eval-lit-fun ρ3 (proj₁ (proj₂ (tseytin-rec (φ ∧ ψ) n))) ≡ eval-nnf-fun ρ (φ ∧ ψ)
      root-eq =
        let open ≡-Reasoning in
        let
          -- relate eval-nnf ρ1 ψ to eval-nnf ρ ψ (ρ1 agrees with ρ on vars < n)
          ψ-ρ1≡ρ : eval-nnf-fun ρ1 ψ ≡ eval-nnf-fun ρ ψ
          ψ-ρ1≡ρ = eval-nnf-equiv-< ρ1 ρ ψ n (⊔<-right pMax) (λ x x<n → IH-ρ1 x x<n)
        in
        begin
          eval-lit-fun ρ3 (Var n2)
        ≡⟨ refl ⟩
          ρ3 n2
        ≡⟨ extend-ρ-hit ρ2 n2 b-val ⟩
          eval-lit-fun ρ2 l1 ∧ᵇ eval-lit-fun ρ2 l2
        ≡⟨ cong₂ _∧ᵇ_ l1-ρ2≡ refl ⟩
          eval-lit-fun ρ1 l1 ∧ᵇ eval-lit-fun ρ2 l2
        ≡⟨ cong₂ _∧ᵇ_ IH-l1 IH-l2 ⟩
          eval-nnf-fun ρ φ ∧ᵇ eval-nnf-fun ρ1 ψ
        ≡⟨ cong (λ k → eval-nnf-fun ρ φ ∧ᵇ k) ψ-ρ1≡ρ ⟩
          eval-nnf-fun ρ φ ∧ᵇ eval-nnf-fun ρ ψ
        ≡⟨ refl ⟩
          eval-nnf-fun ρ (φ ∧ ψ)
        ∎

      bounds : ∀ x → x < n → ρ3 x ≡ ρ x
      bounds x x<n =
        let
          x<n2 : x < n2
          x<n2 = <-≤-trans x<n (≤-trans (tseytin-rec-mono φ n) (tseytin-rec-mono ψ n1))
          step1 = extend-ρ-preserves ρ2 n2 b-val x x<n2
          x<n1 : x < n1
          x<n1 = <-≤-trans x<n (tseytin-rec-mono φ n)
          step2 = IH-ρ2 x x<n1
          step3 = IH-ρ1 x x<n
        in trans (trans step1 step2) step3
  in (ρ3 , (clauses-all , root-eq , bounds))

tseytin-rec-complete (φ ∨ ψ) ρ n pMax =
  let (c1 , l1 , n1) = tseytin-rec φ n
      (c2 , l2 , n2) = tseytin-rec ψ n1
      (ρ1 , (IH-c1 , IH-l1 , IH-ρ1)) = tseytin-rec-complete φ ρ n (⊔<-left pMax)
      pψ<n : max-nnf ψ < n
      pψ<n = ⊔<-right pMax
      pψ<n1 : max-nnf ψ < n1
      pψ<n1 = <-≤-trans pψ<n (tseytin-rec-mono φ n)
      (ρ2 , (IH-c2 , IH-l2 , IH-ρ2)) = tseytin-rec-complete ψ ρ1 n1 pψ<n1
      b-val = eval-lit-fun ρ2 l1 ∨ᵇ eval-lit-fun ρ2 l2
      ρ3 = extend-ρ ρ2 n2 b-val

      l1Bound : max-lit l1 < n1
      l1Bound = proj₂ (tseytin-rec-bounds φ n (⊔<-left pMax))
      c1Bound : max-clauses c1 < n1
      c1Bound = proj₁ (tseytin-rec-bounds φ n (⊔<-left pMax))
      l1-ρ2≡ : eval-lit-fun ρ2 l1 ≡ eval-lit-fun ρ1 l1
      l1-ρ2≡ = eval-lit-equiv-< ρ2 ρ1 l1 n1 l1Bound (λ x x<n1 → IH-ρ2 x x<n1)
      c1-ρ2≡ : eval-clauses-fun ρ2 c1 ≡ eval-clauses-fun ρ1 c1
      c1-ρ2≡ = eval-clauses-equiv-< ρ2 ρ1 c1 n1 c1Bound (λ x x<n1 → IH-ρ2 x x<n1)
      c1-ρ2-true : eval-clauses-fun ρ2 c1 ≡ true
      c1-ρ2-true = trans c1-ρ2≡ IH-c1

      pρ3< : ∀ x → x < n2 → ρ3 x ≡ ρ2 x
      pρ3< x x<n2 = extend-ρ-preserves ρ2 n2 b-val x x<n2
      l2Bound : max-lit l2 < n2
      l2Bound = proj₂ (tseytin-rec-bounds ψ n1 pψ<n1)
      c2Bound : max-clauses c2 < n2
      c2Bound = proj₁ (tseytin-rec-bounds ψ n1 pψ<n1)
      l1Bound<n2 : max-lit l1 < n2
      l1Bound<n2 = <-≤-trans l1Bound (tseytin-rec-mono ψ n1)
      c1Bound<n2 : max-clauses c1 < n2
      c1Bound<n2 = <-≤-trans c1Bound (tseytin-rec-mono ψ n1)

      l1-ρ3≡ : eval-lit-fun ρ3 l1 ≡ eval-lit-fun ρ2 l1
      l1-ρ3≡ = eval-lit-equiv-< ρ3 ρ2 l1 n2 l1Bound<n2 pρ3<
      l2-ρ3≡ : eval-lit-fun ρ3 l2 ≡ eval-lit-fun ρ2 l2
      l2-ρ3≡ = eval-lit-equiv-< ρ3 ρ2 l2 n2 l2Bound pρ3<
      c1-ρ3≡ : eval-clauses-fun ρ3 c1 ≡ eval-clauses-fun ρ2 c1
      c1-ρ3≡ = eval-clauses-equiv-< ρ3 ρ2 c1 n2 c1Bound<n2 pρ3<
      c2-ρ3≡ : eval-clauses-fun ρ3 c2 ≡ eval-clauses-fun ρ2 c2
      c2-ρ3≡ = eval-clauses-equiv-< ρ3 ρ2 c2 n2 c2Bound pρ3<

      c1-ρ3-true : eval-clauses-fun ρ3 c1 ≡ true
      c1-ρ3-true = trans c1-ρ3≡ c1-ρ2-true
      c2-ρ3-true : eval-clauses-fun ρ3 c2 ≡ true
      c2-ρ3-true = trans c2-ρ3≡ IH-c2

      clauses-ρ3-true : eval-clauses-fun ρ3 (c1 ++ c2) ≡ true
      clauses-ρ3-true =
        let open ≡-Reasoning in
        begin
          eval-clauses-fun ρ3 (c1 ++ c2)
        ≡⟨ eval-clauses-++ ρ3 c1 c2 ⟩
          eval-clauses-fun ρ3 c1 ∧ᵇ eval-clauses-fun ρ3 c2
        ≡⟨ cong₂ _∧ᵇ_ c1-ρ3-true c2-ρ3-true ⟩
          true ∧ᵇ true
        ≡⟨ refl ⟩
          true
        ∎

      gate-ρ3-true :
        eval-clauses-fun ρ3 ((Var n2 ∨ Lit (neg-lit l1)) ∷ (Var n2 ∨ Lit (neg-lit l2)) ∷ (¬Var n2 ∨ l1 ∨ Lit l2) ∷ []) ≡ true
      gate-ρ3-true =
        let
          b = eval-lit-fun ρ3 l1
          c = eval-lit-fun ρ3 l2
          x≡ : ρ3 n2 ≡ b ∨ᵇ c
          x≡ =
            let open ≡-Reasoning in
            begin
              ρ3 n2
            ≡⟨ extend-ρ-hit ρ2 n2 b-val ⟩
              b-val
            ≡⟨ cong₂ _∨ᵇ_ (sym l1-ρ3≡) (sym l2-ρ3≡) ⟩
              (eval-lit-fun ρ3 l1 ∨ᵇ eval-lit-fun ρ3 l2)
            ∎
        in
        let open ≡-Reasoning in
        begin
          eval-clauses-fun ρ3
            ((Var n2 ∨ Lit (neg-lit l1)) ∷ (Var n2 ∨ Lit (neg-lit l2)) ∷
             (¬Var n2 ∨ l1 ∨ Lit l2) ∷ [])
        ≡⟨ refl ⟩
          ((ρ3 n2) ∨ᵇ eval-lit-fun ρ3 (neg-lit l1))
          ∧ᵇ (((ρ3 n2) ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
              ∧ᵇ (((not (ρ3 n2)) ∨ᵇ b ∨ᵇ c) ∧ᵇ true))
        ≡⟨ cong
            (λ x → (x ∨ᵇ eval-lit-fun ρ3 (neg-lit l1))
                 ∧ᵇ ((x ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
                     ∧ᵇ (((not x) ∨ᵇ b ∨ᵇ c) ∧ᵇ true)))
            x≡ ⟩
          ((b ∨ᵇ c) ∨ᵇ eval-lit-fun ρ3 (neg-lit l1))
          ∧ᵇ (((b ∨ᵇ c) ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
              ∧ᵇ (((not (b ∨ᵇ c)) ∨ᵇ b ∨ᵇ c) ∧ᵇ true))
        ≡⟨ cong
            (λ u → ((b ∨ᵇ c) ∨ᵇ u)
                 ∧ᵇ (((b ∨ᵇ c) ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
                     ∧ᵇ (((not (b ∨ᵇ c)) ∨ᵇ b ∨ᵇ c) ∧ᵇ true)))
            (eval-neg-lit ρ3 l1) ⟩
          ((b ∨ᵇ c) ∨ᵇ not b)
          ∧ᵇ (((b ∨ᵇ c) ∨ᵇ eval-lit-fun ρ3 (neg-lit l2))
              ∧ᵇ (((not (b ∨ᵇ c)) ∨ᵇ b ∨ᵇ c) ∧ᵇ true))
        ≡⟨ cong
            (λ v → ((b ∨ᵇ c) ∨ᵇ not b)
                 ∧ᵇ (((b ∨ᵇ c) ∨ᵇ v)
                     ∧ᵇ (((not (b ∨ᵇ c)) ∨ᵇ b ∨ᵇ c) ∧ᵇ true)))
            (eval-neg-lit ρ3 l2) ⟩
          ((b ∨ᵇ c) ∨ᵇ not b)
          ∧ᵇ (((b ∨ᵇ c) ∨ᵇ not c)
              ∧ᵇ (((not (b ∨ᵇ c)) ∨ᵇ b ∨ᵇ c) ∧ᵇ true))
        ≡⟨ cong
            (λ t → ((b ∨ᵇ c) ∨ᵇ not b)
                 ∧ᵇ (((b ∨ᵇ c) ∨ᵇ not c) ∧ᵇ t))
            (and-true-right ((not (b ∨ᵇ c)) ∨ᵇ b ∨ᵇ c)) ⟩
          ((b ∨ᵇ c) ∨ᵇ not b)
          ∧ᵇ (((b ∨ᵇ c) ∨ᵇ not c)
              ∧ᵇ ((not (b ∨ᵇ c)) ∨ᵇ b ∨ᵇ c))
        ≡⟨ or-gate-complete b c ⟩
          true
        ∎

      clauses-all : eval-clauses-fun ρ3 (proj₁ (tseytin-rec (φ ∨ ψ) n)) ≡ true
      clauses-all =
        let head = ((Var n2 ∨ Lit (neg-lit l1)) ∷ ((Var n2 ∨ Lit (neg-lit l2)) ∷ ((¬Var n2 ∨ l1 ∨ Lit l2) ∷ []))) in
        subst (λ t → t ≡ true) (sym (eval-clauses-++ ρ3 head (c1 ++ c2))) (cong₂ _∧ᵇ_ gate-ρ3-true clauses-ρ3-true)

      root-eq : eval-lit-fun ρ3 (proj₁ (proj₂ (tseytin-rec (φ ∨ ψ) n))) ≡ eval-nnf-fun ρ (φ ∨ ψ)
      root-eq =
        let open ≡-Reasoning in
        let
          ψ-ρ1≡ρ : eval-nnf-fun ρ1 ψ ≡ eval-nnf-fun ρ ψ
          ψ-ρ1≡ρ = eval-nnf-equiv-< ρ1 ρ ψ n (⊔<-right pMax) (λ x x<n → IH-ρ1 x x<n)
        in
        begin
          eval-lit-fun ρ3 (Var n2)
        ≡⟨ refl ⟩
          ρ3 n2
        ≡⟨ extend-ρ-hit ρ2 n2 b-val ⟩
          eval-lit-fun ρ2 l1 ∨ᵇ eval-lit-fun ρ2 l2
        ≡⟨ cong₂ _∨ᵇ_ l1-ρ2≡ refl ⟩
          eval-lit-fun ρ1 l1 ∨ᵇ eval-lit-fun ρ2 l2
        ≡⟨ cong₂ _∨ᵇ_ IH-l1 IH-l2 ⟩
          eval-nnf-fun ρ φ ∨ᵇ eval-nnf-fun ρ1 ψ
        ≡⟨ cong (λ k → eval-nnf-fun ρ φ ∨ᵇ k) ψ-ρ1≡ρ ⟩
          eval-nnf-fun ρ φ ∨ᵇ eval-nnf-fun ρ ψ
        ≡⟨ refl ⟩
          eval-nnf-fun ρ (φ ∨ ψ)
        ∎

      bounds : ∀ x → x < n → ρ3 x ≡ ρ x
      bounds x x<n =
        let
          x<n2 : x < n2
          x<n2 = <-≤-trans x<n (≤-trans (tseytin-rec-mono φ n) (tseytin-rec-mono ψ n1))
          step1 = extend-ρ-preserves ρ2 n2 b-val x x<n2
          x<n1 : x < n1
          x<n1 = <-≤-trans x<n (tseytin-rec-mono φ n)
          step2 = IH-ρ2 x x<n1
          step3 = IH-ρ1 x x<n
        in trans (trans step1 step2) step3
  in (ρ3 , (clauses-all , root-eq , bounds))

prove-and : ∀ {a b : Bool} → a ≡ true → b ≡ true → a ∧ᵇ b ≡ true
prove-and {true} {true} refl refl = refl

tseytin-complete-lemma : ∀ φ ρ → eval-nnf-fun ρ φ ≡ true → Σ FunAssignment (λ ρ' → eval-cnf-fun ρ' (tseytin φ) ≡ true)
tseytin-complete-lemma φ ρ p = 
  let
      max< : max-nnf φ < suc (max-nnf φ)
      max< = Data.Nat.s≤s (≤-refl {max-nnf φ})
      (ρ' , (clauses-p , root-eq , bounds-eq)) = tseytin-rec-complete φ ρ (suc (max-nnf φ)) max<
      root-true = trans root-eq p
      step1 = eval-list-to-cnf ρ' (Lit (proj₁ (proj₂ (tseytin-rec φ (suc (max-nnf φ)))))) (proj₁ (tseytin-rec φ (suc (max-nnf φ))))
  in (ρ' , (trans step1 (prove-and root-true clauses-p)))

tseytin-complete-fun : ∀ φ -> SatisfiableNNF-Fun φ → SatisfiableCNF-Fun (tseytin φ)
tseytin-complete-fun φ (ρ , p) = tseytin-complete-lemma φ ρ p

-- equisatisfiability: completeness & soundness.
tseytin-equisatisfiable : ∀ φ → (SatisfiableNNF-Fun φ → SatisfiableCNF-Fun (tseytin φ)) × (SatisfiableCNF-Fun (tseytin φ) → SatisfiableNNF-Fun φ)
tseytin-equisatisfiable φ = (tseytin-complete-fun φ , tseytin-sound-fun φ)
