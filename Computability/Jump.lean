import Computability.Encoding
import Mathlib.Computability.Reduce
import Mathlib.Computability.Halting

import Mathlib.Data.PFun

open Computability
open Classical

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
-- def recursively_enumerable_in (O : Set (ℕ →. ℕ)) (A : Set ℕ) :=
--   ∃ f, (RecursiveIn O f) ∧ A = f.Dom

/-
A set A is recursively enumerable in a family of partial recursive functions `X` if its characteristic
function is recursive in `X`.
-/
-- def recursively_enumerable_in₁ (X : α → ℕ →. ℕ) (A : Set ℕ) :=
--   ∃ f, (RecursiveIn (Set.range X) f) ∧ A = f.Dom

/-
A set A is re in a single partial recursive function g if its characteristic function is recursive in g.
-/
-- def recursively_enumerable_in₂ (g : ℕ →. ℕ) (A : ℕ → Prop) :=
--  ∃ f, (RecursiveIn {g} f) ∧ A = f.Dom

/-
A set A is recursively enumerable if its characteristic function is recursive in the empty set.
-/
-- def recursively_enumerable (A : Set ℕ) :=
--   ∃ f, (RecursiveIn {} f) ∧ A = f.Dom


/-
The jump of f is the diagonal of the universal machine relative to f:
  f⌜ n = evalo (λ _ => f) (decodeCodeo n) n.
Its domain is the set of n where the n-th oracle program halts on input n with oracle f, ie. the halting
problem relative to f.
-/
-- noncomputable def jump (f : ℕ →. ℕ) : ℕ →. ℕ := λ n =>
--   let part := evalo f (decodeCodeo (Nat.unpair n).1) (Nat.unpair n).2
--   if part.Dom then part >>= (Nat.succ:PFun ℕ ℕ) else 0
noncomputable def jump (f : ℕ →. ℕ) : ℕ → ℕ := λ n =>
  let part := evalo f (decodeCodeo (Nat.unpair n).1) (Nat.unpair n).2
  if part.Dom then Nat.succ (part.get _) else 0

-- theorem jump_totality (f : ℕ →. ℕ) : (jump f).Dom = ℕ := by
--   rw [@Set.coe_eq_subtype]
--   apply?
--   -- rw [if_false_left]
--   exact?

/-
The oracle corresponding to a decidable set A ⊆ ℕ, returning 0 on elements of A and undefined elsewhere.
-/
-- def setOracle (A : ℕ → Prop) [DecidablePred A] : ℕ →. ℕ :=
--   λ n => if A n then Part.some 0 else Part.none

-- /-
-- The jump of a decidable set A ⊆ ℕ: the set of n such that the n-th oracle program halts on input n with oracle A.
-- -/
-- def jumpSet (A : ℕ → Prop) [DecidablePred A] : ℕ → Prop :=
--   λ n => (evalo (λ (_ : Unit) => setOracle A) (decodeCodeo n) n).Dom

/-
Wₑᶠ is the domain of the eth partial function recursive in the oracle family {fₐ}.
-/
abbrev W (e : ℕ) (f : ℕ →. ℕ) := (evalo f (decodeCodeo e)).Dom

-- Theorems to prove (2.3 Jump Theorem in Soare Recursively Enumerable Sets and Degrees)
-- 1. f⌜ is recursive in f
-- 2. ¬(f⌜ ≤ f)
-- 3. g is re in f iff g ≤₁ f⌜
-- 4. if g is re in f and f ≤ᵀ h then g is re in h
-- 5. g ≤ᵀ f ↔ g⌜ ≤₁ f⌜
-- 6. If g ≡ᵀ f then g⌜ ≡₁ f⌜
-- 7. ...

notation:100 f"⌜" => jump f

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]
theorem Primrec.projection {f : α → β → σ} {a:α} (h:Primrec₂ f) : Primrec (f a) := by
  refine Primrec₂.comp h ?_ ?_
  · exact const a
  · exact Primrec.id



-- theorem jump_recIn (f : ℕ →. ℕ) : f ≤ᵀ (f⌜) := by sorry
-- theorem jump_recIn (f : ℕ →. ℕ) : f ≤ᵀ (f⌜) := by
--   have main: RecursiveIn (jump f) (f) := by
--     have giseq: f = (fun x => Nat.pair (encodeCodeo (codeo.oracle)) x >>= (jump f)) := by
--       funext xs
--       simp
--       rw [jump]
--       simp
--       -- rw [decodeCodeo.eq_def]
--       simp
--       constructor

--     nth_rewrite 2 [giseq]
--     apply RecursiveIn.comp
--     · constructor
--       simp
--     · simp
--       apply Nat.Partrec.recursiveIn
--       refine Partrec.nat_iff.mp ?_
--       refine Partrec.comp ?_ ?_
--       · exact Partrec.some
--       · refine Primrec.to_comp ?_
--         rw [encodeCodeo]
--         simp
--         exact Primrec.projection Primrec₂.natPair
--     -- sorry
--   exact main


theorem test01 (x:ℕ): Nat.succ x ≠ 0 := by
  exact Ne.symm (Nat.zero_ne_add_one x)

open Part
theorem test0 (x:Part ℕ): (x >>= (Nat.succ:PFun ℕ ℕ) = Part.some 0) = (False) := by

  cases eq_none_or_eq_some x
  case inl h =>
    rw [h]
    simp
    -- rw?

    -- exact?
  case inr h =>
    rcases h with ⟨x2,hx2⟩
    rw [hx2]
    simp




theorem test1 (x:ℕ): (if ((if p then x+1 else 0)=0) then y else z) = (if p then z else y) := by
  simp

theorem test2 (x:Part ℕ): (if ((if p then (x >>= (Nat.succ:PFun ℕ ℕ)) else Part.some 0)=Part.some 0) then y else z) = (if p then z else y) := by
  simp
  -- rw [test0]
  have hf (x:Part ℕ) : ((if p then (x >>= (Nat.succ:PFun ℕ ℕ)) else Part.some 0)=Part.some 0) → ¬ p := by
    simp
    -- simp [test0]
    refine fun a ↦ ?_
    simp only [test0] at a
    exact?
  intro
  -- rw [test0]
  -- simp [test0]
  -- apply test0
  exact?
  -- refine ite_congr rfl ?_ ?_

  -- apply [rfl]
  -- exact?
  -- rw?
  -- apply?
  -- exact?

def Nat.dec : (ℕ → ℕ) := fun n ↦ n-1

theorem jump_recIn (f : ℕ →. ℕ) : f ≤ᵀ (f⌜) := by

  have f_eq_f': f = (fun x =>
    let computation := Nat.pair (encodeCodeo (codeo.oracle)) x >>= (jump f);
    if (computation=0) then Part.none else computation >>= (Nat.dec:PFun ℕ ℕ)) := by
      -- funext xs
      -- simp [Nat]
      simp [jump]
      rw [test0]
      -- simp
      -- simp only [jump]
      -- simp


      -- simp only [Nat.add_one_ne_zero]
      simp!

      have h0 :  := by exact?
      -- rw [decodeCodeo_encodeCodeo]
      refine PFun.ext' ?_ ?_
      · simp [evalo]
        refine fun a ↦ ?_
        refine Iff.symm ((fun {a b} ↦ iff_iff_implies_and_implies.mpr) ?_)
        constructor
        · intro h
          have h2 : (((f a).Dom → f a + 1) = 0) ∨ ¬ (((f a).Dom → f a + 1) = 0) := Classical.em (((f a).Dom → f a + 1) = 0)
          -- classical.em
          cases h2
          case inl h3 =>

            rw [h3] at h

            exact?
          exact?
        exact?

      exact?



      -- rw [decodeCodeo.eq_def]
      simp
      constructor

theorem k0lek (f : ℕ →. ℕ) : (f⌜) ≤ᵀ  (λ n => evalo (λ _ : Unit => f) (decodeCodeo n) n) := by
  let k := λ n => evalo (λ _ : Unit => f) (decodeCodeo n) n
  let h := λ (ex:ℕ) => encodeCodeo (codeo.comp (decodeCodeo ex.unpair.1) (const ex.unpair.2))
  -- h takes as input (e,x), and outputs the index for the function which calculates and returns [e:f](x).
  -- which is... encodeCodeo (codeo.comp (decodeCodeo e) (codeo.succ codeo.succ ... codeo.zero))
  -- which is... encodeCodeo (codeo.comp (decodeCodeo e) (const x))
  have k0_intermsof_k : f⌜ = k ∘ h := by
    simp [k, h]
    rw [@Function.comp_def]
    simp [decodeCodeo_encodeCodeo]
    simp [evalo]
    simp [evalo_const]
    exact rfl
  simp [k0_intermsof_k]
  sorry




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
