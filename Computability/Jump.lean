import Computability.Encoding
import Mathlib.Computability.Reduce
import Mathlib.Computability.Halting

open Computability

/-
In this file we define the jump operator (⌜) for partial recursive functions and prove its main properties.

We can identify part rec functions with recursively enumerable sets by taking their domain,
if f : ℕ →. ℕ, then dom(f) : ℕ → Prop := λ n => n ∈ f.Dom. These are the terms in which we
state the jump theorems:
-/

/-
A set A is recursively enumerable in a set of partial recursive functions `O` if its characteristic
function is recursive in `O`.
-/
def recursively_enumerable_in (O : Set (ℕ →. ℕ)) (A : Set ℕ) :=
  ∃ f, (RecursiveIn O f) ∧ A = f.Dom

/-
A set A is recursively enumerable in a family of partial recursive functions `X` if its characteristic
function is recursive in `X`.
-/
def recursively_enumerable_in₁ (X : α → ℕ →. ℕ) (A : Set ℕ) :=
  ∃ f, (RecursiveIn (Set.range X) f) ∧ A = f.Dom

/-
A set A is re in a single partial recursive function g if its characteristic function is recursive in g.
-/
def recursively_enumerable_in₂ (g : ℕ →. ℕ) (A : ℕ → Prop) :=
 ∃ f, (RecursiveIn {g} f) ∧ A = f.Dom

/-
A set A is recursively enumerable if its characteristic function is recursive in the empty set.
-/
def recursively_enumerable (A : Set ℕ) :=
  ∃ f, (RecursiveIn {} f) ∧ A = f.Dom

/-
The jump of f is the diagonal of the universal machine relative to f:
  f⌜ n = evalo (λ _ => f) (decodeCodeo n) n.
Its domain is the set of n where the n-th oracle program halts on input n with oracle f, ie. the halting
problem relative to f.
-/
def jump (f : ℕ →. ℕ) : ℕ →. ℕ :=
  λ n => evalo (λ _ : Unit => f) (decodeCodeo n) n

/-
The oracle corresponding to a decidable set A ⊆ ℕ, returning 0 on elements of A and undefined elsewhere.
-/
def setOracle (A : ℕ → Prop) [DecidablePred A] : ℕ →. ℕ :=
  λ n => if A n then Part.some 0 else Part.none

/-
The jump of a decidable set A ⊆ ℕ: the set of n such that the n-th oracle program halts on input n with oracle A.
-/
def jumpSet (A : ℕ → Prop) [DecidablePred A] : ℕ → Prop :=
  λ n => (evalo (λ (_ : Unit) => setOracle A) (decodeCodeo n) n).Dom

/-
Wₑᶠ is the domain of the eth partial function recursive in the oracle family {fₐ}.
-/
abbrev W [Primcodable α] (e : ℕ) (f : α → ℕ →. ℕ) := (evalo f (decodeCodeo e)).Dom

-- Theorems to prove (2.3 Jump Theorem in Soare Recursively Enumerable Sets and Degrees)
-- 1. f⌜ is recursive in f
-- 2. ¬(f⌜ ≤ f)
-- 3. g is re in f iff g ≤₁ f⌜
-- 4. if g is re in f and f ≤ᵀ h then g is re in h
-- 5. g ≤ᵀ f ↔ g⌜ ≤₁ f⌜
-- 6. If g ≡ᵀ f then g⌜ ≡₁ f⌜
-- 7. ...

notation:100 f"⌜" => jump f

theorem jump_recIn (f : ℕ →. ℕ) : f ≤ᵀ (f⌜) := by sorry

theorem jump_not_reducible (f : ℕ →. ℕ) : ¬(f⌜ ≤ᵀ f) := by sorry

theorem re_iff_one_one_jump  (A : Set ℕ) (f : ℕ →. ℕ) :
recursively_enumerable_in₂ f A ↔ OneOneReducible A (f⌜).Dom := by sorry

theorem re_in_trans (A : Set ℕ) (f h : ℕ →. ℕ) :
  recursively_enumerable_in₂ f A →
  f ≤ᵀ h →
  recursively_enumerable_in₂ h A := by
  intro freInA fh
  simp [recursively_enumerable_in₂] at *
  obtain ⟨g, hg, hA⟩ := freInA
  use g
  constructor
  have tred : g ≤ᵀ f := by
    simp [TuringReducible]
    assumption
  exact TuringReducible.trans tred fh
  exact hA

theorem jump_reducible_iff (f g : ℕ →. ℕ) :
  g ≤ᵀ f ↔ g⌜ ≤ᵀ f⌜ := by sorry

theorem jump_equiv (f g : ℕ →. ℕ) :
  g ≡ᵀ f ↔ g⌜ ≡ᵀ f⌜ := by sorry

#check StateM
