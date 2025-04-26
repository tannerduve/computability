-- import Computability.Encoding
-- import Mathlib.Computability.Reduce
-- import Computability.TuringDegrees
-- import Mathlib.Computability.Halting

-- #check OneOneReducible
-- notation:50 f "≤₁" g => OneOneReducible f g
-- notation f "≡₁" g => OneOneEquiv f g

-- /-
-- In this file we define the jump operator (⌜) for partial recursive functions and prove its main properties.

-- Theorems to prove (2.3 Jump Theorem in Soare Recursively Enumerable Sets and Degrees)
-- 1. f⌜ is recursively enumerable in f
-- 2. ¬(f⌜ ≤ f)
-- 3. g is re in f iff g ≤₁ f⌜
-- 4. if g is re in f and f ≤ᵀ h then g is re in h
-- 5. g ≤ᵀ f ↔ g⌜ ≤₁ f⌜
-- 6. If g ≡ᵀ f then g⌜ ≡₁ f⌜
-- 7. ...

-- We can identify part rec functions with recursively enumerable sets by taking their domain,
-- if f : ℕ →. ℕ, then dom(f) : ℕ → Prop := λ n => n ∈ f.Dom. These are the terms in which we
-- state the jump theorems:
-- -/

-- #check ComputablePred.halting_problem_re

-- def recursively_enumerable_in (g : ℕ →. ℕ) (A : ℕ → Prop) :=
--   ∃ f, (RecursiveIn g f) ∧ (∀ n, A n ↔ n ∈ f.Dom)

-- abbrev W (e : ℕ) (f : ℕ →. ℕ) := (φ f e).Dom

-- notation f "≤ᴿ" g => OneOneReducible f g

-- def dom (f : ℕ →. ℕ) : ℕ → Prop :=
--   λ n => n ∈ f.Dom


-- lemma evalo_rec_in (g : ℕ →. ℕ) (c : codeo) :
--   RecursiveIn g (evalo g c) := by
--   induction c
--   case zero => exact RecursiveIn.zero
--   case succ => exact RecursiveIn.succ
--   case left => exact RecursiveIn.left
--   case right => exact RecursiveIn.right
--   case pair c1 c2 ih_c1 ih_c2 =>
--     exact RecursiveIn.pair ih_c1 ih_c2
--   case comp c1 c2 ih_c1 ih_c2 =>
--     exact RecursiveIn.comp ih_c1 ih_c2
--   case prec c1 c2 ih_c1 ih_c2 =>
--     exact RecursiveIn.prec ih_c1 ih_c2
--   case rfind' c ih_c =>
--     sorry


-- notation:50 g"⌜" => jump g

-- theorem jump_re_in (g : ℕ →. ℕ) :
--   recursively_enumerable_in g (dom (jump g)) := by
--   unfold recursively_enumerable_in at *
--   use (λ n => (φ g n) n)
--   constructor
--   unfold φ
--   sorry

-- theorem jump_not_reducible (g : ℕ →. ℕ) :
--   ¬ (jump g ≤ᵀ g) := by
--   sorry

-- theorem re_iff_one_one_reducible (g f : ℕ →. ℕ) :
--   (recursively_enumerable_in g (λ n => n ∈ f.Dom)) ↔ OneOneReducible (dom g) (dom (jump f)) :=
--   sorry

-- theorem re_in (g f h : ℕ →. ℕ) :
--   recursively_enumerable_in g (dom f) → f ≤ᵀ h → recursively_enumerable_in g (dom h) :=
-- sorry

-- theorem turing_reducible_iff_one_one_reducible (g f : ℕ →. ℕ) :
--   g ≤ᵀ f ↔ OneOneReducible (dom (jump f)) (dom (jump f)) :=
--   sorry

-- theorem if_turing_equivalent_then_one_one_equivalent (g f : ℕ →. ℕ) :
--   g ≡ᵀ f → dom (jump g) ≡₁ dom (jump f) :=
--   sorry
