import Computability.Encoding

/-
We define some relativized versions of basic constructs in computability
-/

def recursively_enumerable_in (g : ℕ →. ℕ) (A : ℕ → Prop) :=
  ∃ f, (RecursiveIn g f) ∧ (∀ n, A n ↔ n ∈ f.Dom)

abbrev W (e : ℕ) (f : ℕ →. ℕ) := (φ f e).Dom

notation f "≤ᴿ" g => OneOneReducible f g
