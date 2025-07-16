import Computability.SingleOracle.Encoding
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
@[simp] noncomputable def jump (f : ℕ →. ℕ) : ℕ → ℕ := λ n =>
  let part := evalo f (decodeCodeo (Nat.unpair n).1) (Nat.unpair n).2
  dite part.Dom (λ proof => Nat.succ $ part.get proof) (λ _ => 0)
  -- if part.Dom then Nat.succ (part.get _) else 0

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



def Nat.dec : (ℕ → ℕ) := fun n ↦ n-1

/-
There are lots of primrec theorems we would like to use like

theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Primrec c) (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) else (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

-- Now, if f is primrec + oracle g,
It'd be nice to be able to automatically extend all of these to smth like

theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : PrimrecOracle O c) (hf : PrimrecOracle O f)
    (hg : PrimrecOracle O g) : PrimrecOracle O fun a => bif (c a) then (f a) else (g a)

-/


/- Partially recursive partial functions `α → σ` between `Primcodable` types -/
-- def PartrecIn2 {β τ α σ} [Primcodable β] [Primcodable τ] [Primcodable α] [Primcodable σ] (g : β →. τ) (f : α →. σ) :=
--   RecursiveIn (fun n => Part.bind (Encodable.decode (β := β) n) fun a => (g a).map Encodable.encode) fun n => Part.bind (Encodable.decode (α := α) n) fun a => (f a).map Encodable.encode
-- def PartrecIn1 {α σ} [Primcodable α] [Primcodable σ] (g : ℕ→.ℕ) (f : α →. σ) :=
--   RecursiveIn g fun n => Part.bind (Encodable.decode (α := α) n) fun a => (f a).map Encodable.encode

-- instance : OfNat (Part ℕ) m where ofNat := Part.some (m)


@[simp] lemma some_zero : (0 : Part ℕ) = Part.some 0 := by exact rfl
@[simp] lemma RecursiveIn.some2 (O:ℕ→.ℕ) (f:ℕ→ℕ): RecursiveIn O fun x => Part.some (f x) := by sorry
@[simp] lemma RecursiveIn.totalComp {O:ℕ→.ℕ} {f g:ℕ→ℕ} (h1: RecursiveIn O f) (h2: RecursiveIn O g) : (RecursiveIn O ↑(f∘g)) := by sorry
@[simp] lemma RecursiveIn.totalToPartComp {O f:ℕ→.ℕ} {g:ℕ→ℕ} (h1: RecursiveIn O f) (h2: RecursiveIn O g) : (RecursiveIn O ↑(f∘g)) := by sorry
-- lemma someTotalDomain {f:ℕ→ℕ} : PFun.Dom (Part.some ∘ f) = ℕ := by


theorem RecursiveIn.ite {f g : ℕ→.ℕ} {c:ℕ→ℕ} (hc : RecursiveIn O c) (hf : RecursiveIn O f)
    (hg : RecursiveIn O g) : RecursiveIn O fun a => if (c a=0) then (f a) else (g a) := by sorry


theorem partcomp (O: ℕ →. ℕ) (f:ℕ→ℕ) (hf : RecursiveIn O f) : RecursiveIn g (Part.some ∘ f) := by
  sorry


theorem jump_recIn (f : ℕ →. ℕ) : f ≤ᵀ (f⌜) := by
  let compute := (jump f) ∘ (Nat.pair (encodeCodeo (codeo.oracle)));
  let f':ℕ→.ℕ := (fun x => if compute x=0 then Part.none else (Nat.pred ∘ compute) x)
  have f_eq_f': f = f' := by
      simp [f']
      funext xs
      cases Classical.em (compute xs = 0) with
      | inl h =>
        simp [h]
        simp [compute, evalo] at h
        exact Part.eq_none_iff'.mpr h
      | inr h =>
        simp [compute, evalo]
        simp [compute, evalo] at h
        simp [h]

  have compute_recIn_fJump : compute ≤ᵀ (f⌜) := by
    apply RecursiveIn.totalComp
    · exact RecursiveIn.oracle
    · apply RecursiveIn.some2

  have f'_recIn_fJump : f' ≤ᵀ (f⌜) := by
    simp only [f',TuringReducible]
    apply RecursiveIn.ite
    · exact compute_recIn_fJump
    · exact RecursiveIn.none
    · apply RecursiveIn.totalComp
      · apply Nat.Partrec.recursiveIn
        apply Nat.Partrec.of_primrec
        exact Nat.Primrec.pred
      · exact compute_recIn_fJump

  exact RecursiveIn.of_eq f'_recIn_fJump (congrFun (id (Eq.symm f_eq_f')))





-- theorem k0lek (f : ℕ →. ℕ) : (f⌜) ≤ᵀ  (λ n => evalo (λ _ : Unit => f) (decodeCodeo n) n) := by
--   let k := λ n => evalo (λ _ : Unit => f) (decodeCodeo n) n
--   let h := λ (ex:ℕ) => encodeCodeo (codeo.comp (decodeCodeo ex.unpair.1) (const ex.unpair.2))
--   -- h takes as input (e,x), and outputs the index for the function which calculates and returns [e:f](x).
--   -- which is... encodeCodeo (codeo.comp (decodeCodeo e) (codeo.succ codeo.succ ... codeo.zero))
--   -- which is... encodeCodeo (codeo.comp (decodeCodeo e) (const x))
--   have k0_intermsof_k : f⌜ = k ∘ h := by
--     simp [k, h]
--     rw [@Function.comp_def]
--     simp [decodeCodeo_encodeCodeo]
--     simp [evalo]
--     simp [evalo_const]
--     exact rfl
--   simp [k0_intermsof_k]
--   sorry




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
