import Computability.SingleOracle.RecursiveInTheorems
-- import Computability.SingleOracle.Encoding
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



@[simp] noncomputable def jump (f : ℕ →. ℕ) : ℕ → ℕ := λ n =>
  let part := evalo f (decodeCodeo (Nat.unpair n).1) (Nat.unpair n).2
  dite part.Dom (λ proof => Nat.succ $ part.get proof) (λ _ => 0)
noncomputable abbrev K0 (O : ℕ →. ℕ) := jump O

notation:100 f"⌜" => jump f










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


theorem RecursiveIn.jumpDecodeIte {O} {compute:ℕ→ℕ} (compute_recIn_fJump: compute ≤ᵀ O): RecursiveIn O fun x ↦ if compute x = 0 then Part.none else ↑(some ((Nat.pred ∘ compute) x)) := by
  apply RecursiveIn.ite
  · exact compute_recIn_fJump
  · exact RecursiveIn.none
  · apply RecursiveIn.totalComp
    · apply Nat.Partrec.recursiveIn
      apply Nat.Partrec.of_primrec
      exact Nat.Primrec.pred
    · exact compute_recIn_fJump

theorem jump_recIn (f : ℕ →. ℕ) : f ≤ᵀ (f⌜) := by
  let compute := (jump f) ∘ (Nat.pair (encodeCodeo (codeo.oracle)));
  let f':ℕ→.ℕ := (fun x => if compute x=0 then Part.none else (Nat.pred ∘ compute) x)

  have f_eq_f': f = f' := by
      simp only [f']
      funext xs
      cases Classical.em (compute xs = 0) with
      | inl h =>
        simp only [h]
        simp only [compute, Function.comp_apply, jump, Nat.unpair_pair, decodeCodeo_encodeCodeo, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false] at h
        exact Part.eq_none_iff'.mpr h
      | inr h =>
        simp only [compute,Function.comp_apply, jump, Nat.unpair_pair, decodeCodeo_encodeCodeo,Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false,imp_false, Nat.pred_eq_sub_one, Part.coe_some, ite_not, evalo]
        simp only [compute, Function.comp_apply, jump, Nat.unpair_pair, decodeCodeo_encodeCodeo,Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false,imp_false, Decidable.not_not, evalo] at h
        simp only [h,↓reduceIte, ↓reduceDIte, add_tsub_cancel_right, Part.some_get]

  have compute_recIn_fJump : compute ≤ᵀ (f⌜) := by
    apply RecursiveIn.totalComp
    · exact RecursiveIn.oracle
    · apply RecursiveIn.of_primrec Nat.Primrec.pair_proj

  have f'_recIn_fJump : f' ≤ᵀ (f⌜) := by
    simp only [f',TuringReducible]
    exact RecursiveIn.jumpDecodeIte compute_recIn_fJump

  exact RecursiveIn.of_eq f'_recIn_fJump (congrFun (id (Eq.symm f_eq_f')))



@[simp] noncomputable def K (O : ℕ →. ℕ) : ℕ → ℕ := λ n =>
  let part := evalo O (decodeCodeo n) n
  dite part.Dom (λ proof => Nat.succ $ part.get proof) (λ _ => 0)

theorem OracleRecursiveInK (O : ℕ →. ℕ) : O ≤ᵀ (K O) := by
  let compute := (K O) ∘ codeo_calculate ∘ Nat.pair (encodeCodeo codeo.oracle)
  let h:ℕ→.ℕ := (fun x => if compute x=0 then Part.none else (Nat.pred ∘ compute) x)

  have main : O = h := by

    simp only [h]
    funext xs
    cases Classical.em (compute xs = 0) with
    | inl h =>
        simp only [h]
        simp only [compute, Function.comp_apply, K, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, codeo_calculate', decodeCodeo_encodeCodeo] at h
        exact Part.eq_none_iff'.mpr h
      | inr h =>
        simp only [compute]
        simp only [Function.comp_apply, K, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero,
          one_ne_zero, and_false, imp_false, Nat.pred_eq_sub_one, Part.coe_some, ite_not]
        simp only [compute] at h
        simp only [Function.comp_apply, K, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero,
          one_ne_zero, and_false, imp_false, Decidable.not_not] at h

        simp only [h]
        simp only [codeo_calculate']
        simp only [↓reduceIte, ↓reduceDIte, decodeCodeo_encodeCodeo, add_tsub_cancel_right,
          Part.some_get]
        exact rfl

  have compute_recIn_KO : compute ≤ᵀ (K O) := by
    simp only [compute, TuringReducible]

    apply RecursiveIn.totalComp
    · exact RecursiveIn.oracle
    · apply RecursiveIn.totalComp
      · exact RecursiveIn.of_primrec Primrec.codeo_calculate
      · rw [RecursiveIn.pair']
        apply RecursiveIn.pair
        · simp only [encodeCodeo]
          exact RecursiveIn.of_primrec (Nat.Primrec.const 4)
        · exact RecursiveIn.id

  rw (config := {occs := .pos [1]}) [main]
  simp only [h]
  exact RecursiveIn.jumpDecodeIte compute_recIn_KO

theorem K_leq_K0 (O : ℕ →. ℕ) : (K O) ≤ᵀ (K0 O) := by
  let h:ℕ→ℕ := (fun x => Nat.pair x x)

  have construction_eq_goal : K O = O⌜ ∘ h := by
    simp only [h]
    funext xs
    simp only [K]
    simp only [Nat.succ_eq_add_one, Function.comp_apply, jump, Nat.unpair_pair]

  rw [construction_eq_goal]
  simp only [h]
  rw [TuringReducible]
  refine RecursiveIn.totalComp ?_ ?_
  · exact RecursiveIn.oracle
  · exact RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id)


theorem K0_leq_K (O : ℕ →. ℕ) : (K0 O) ≤ᵀ (K O) := by
  let compute := (K O) ∘ codeo_calculate
  let h:ℕ→.ℕ := (compute)

  have main : O⌜ = h := by
    simp only [h]
    funext xs
    cases Classical.em (compute xs = 0) with
    | inl h =>
        simp only [PFun.coe_val, jump, Nat.succ_eq_add_one, Part.some_inj]
        simp only [h]
        simp only [dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false]
        simp only [compute] at h
        simp only [Function.comp_apply, K, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false] at h
        rw [show xs = Nat.pair (xs.unpair.1) (xs.unpair.2) from Eq.symm (Nat.pair_unpair xs)] at h
        simp only [codeo_calculate'] at h
        exact h
    | inr h =>
      simp only [PFun.coe_val, jump, Nat.succ_eq_add_one, Part.some_inj]
      simp only [compute]
      simp only [compute] at h
      simp only [Function.comp_apply, K, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, Decidable.not_not] at h
      simp only [Function.comp_apply, K, Nat.succ_eq_add_one]
      simp only [h]
      rw [show xs = Nat.pair (xs.unpair.1) (xs.unpair.2) from Eq.symm (Nat.pair_unpair xs)] at h
      simp only [codeo_calculate'] at h
      simp only [h]
      have temp : codeo_calculate xs = codeo_calculate (Nat.pair (xs.unpair.1) (xs.unpair.2)) := by exact rfl
      simp only [temp]
      simp only [codeo_calculate']

  have compute_recIn_KO : compute ≤ᵀ (K O) := by
    simp only [compute, TuringReducible]

    apply RecursiveIn.totalComp
    · exact RecursiveIn.oracle
    · exact RecursiveIn.of_primrec Primrec.codeo_calculate

  rw [main]
  simp only [h]
  exact compute_recIn_KO

theorem K0_eq_K {O} : (K O) ≡ᵀ (K0 O) := ⟨K_leq_K0 O,K0_leq_K O⟩


theorem jump_not_reducible (f:ℕ→.ℕ) : ¬(f⌜ ≤ᵀ f) := by
  intro jump_reducible
  let g : (ℕ→.ℕ) := fun (x:ℕ) => if (f⌜) (Nat.pair x x) = 0 then 0 else Part.none

  have g_recIn_f : RecursiveIn f g := by
    simp only [g]
    apply RecursiveIn.ite
    · apply RecursiveIn.totalComp' jump_reducible
      exact RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id)
    · exact RecursiveIn.zero
    · exact RecursiveIn.none

  have exists_index_for_g : ∃ c : ℕ, evalo f c = g := by exact (exists_codeN_rel f g).mp g_recIn_f
  rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

  cases Classical.em (g index_g).Dom with
  | inl h =>
    have contra : g index_g = Part.none := by
      simp only [g]
      simp only [jump, Nat.unpair_pair, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero,one_ne_zero, and_false, imp_false, ite_not, ite_eq_left_iff]
      simp only [index_g_is_g]
      exact fun a ↦ False.elim (a h)
    rw [contra] at h
    exact h
  | inr h =>
    have contra : g index_g = 0 := by
      simp only [g]
      simp only [jump, Nat.unpair_pair, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero,one_ne_zero, and_false, imp_false, ite_not, ite_eq_left_iff]
      simp only [index_g_is_g]
      exact if_neg h
    rw [contra] at h
    exact h trivial


-- theorem re_iff_one_one_jump  (A : Set ℕ) (f : ℕ →. ℕ) :
-- recursively_enumerable_in₂ f A ↔ OneOneReducible A (f⌜).Dom := by sorry

-- theorem re_in_trans (A : Set ℕ) (f h : ℕ →. ℕ) :
--   recursively_enumerable_in₂ f A →
--   f ≤ᵀ h →
--   recursively_enumerable_in₂ h A := by
--   intro freInA fh
--   simp [recursively_enumerable_in₂] at *
--   obtain ⟨g, hg, hA⟩ := freInA
--   use g
--   constructor
--   have tred : g ≤ᵀ f := by
--     simp [TuringReducible]
--     assumption
--   exact TuringReducible.trans tred fh
--   exact hA
