import Computability.TuringDegrees
import Computability.Encoding
import Computability.Misc
import Mathlib.Computability.Reduce

#check OneOneReducible
notation:50 f "≤₁" g => OneOneReducible f g
notation f "≡₁" g => OneOneEquiv f g

/-
In this file we define the jump operator (⌜) for partial recursive functions and prove its main properties.

Theorems to prove (2.3 Jump Theorem in Soare Recursively Enumerable Sets and Degrees)
1. f⌜ is recursively enumerable in f
2. ¬(f⌜ ≤ f)
3. g is re in f iff g ≤₁ f⌜
4. if g is re in f and f ≤ᵀ h then g is re in h
5. g ≤ᵀ f ↔ g⌜ ≤₁ f⌜
6. If g ≡ᵀ f then g⌜ ≡₁ f⌜
7. ...

We can identify part rec functions with recursively enumerable sets by taking their domain,
if f : ℕ →. ℕ, then dom(f) : ℕ → Prop := λ n => n ∈ f.Dom. These are the terms in which we
state the jump theorems:
-/

def dom (f : ℕ →. ℕ) : ℕ → Prop :=
  λ n => n ∈ f.Dom

def jump (f : ℕ →. ℕ) : ℕ →. ℕ :=
λ e => (φ f e) e
notation:50 g"⌜" => jump g

lemma jump_re_in (g : ℕ →. ℕ) :
  recursively_enumerable_in g (dom (jump g)) := by
  sorry


lemma jump_not_reducible (g : ℕ →. ℕ) :
  ¬ (jump g ≤ᵀ g) :=
  sorry

lemma re_iff_one_one_reducible (g f : ℕ →. ℕ) :
  (recursively_enumerable_in g (λ n => n ∈ f.Dom)) ↔ OneOneReducible (dom g) (dom (jump f)) :=
  sorry

lemma re_in (g f h : ℕ →. ℕ) :
  recursively_enumerable_in g (dom f) → f ≤ᵀ h → recursively_enumerable_in g (dom h) :=
  sorry

lemma turing_reducible_iff_one_one_reducible (g f : ℕ →. ℕ) :
  g ≤ᵀ f ↔ OneOneReducible (dom (jump f)) (dom (jump f)) :=
  sorry

lemma if_turing_equivalent_then_one_one_equivalent (g f : ℕ →. ℕ) :
  g ≡ᵀ f → dom (jump g) ≡₁ dom (jump f) :=
  sorry
