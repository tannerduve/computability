import Computability.SingleOracle.Jump
import Mathlib.Order.Basic

open scoped Computability
open Classical
open Nat.RecursiveIn.Code
namespace Computability

-- definitions
noncomputable def χ (O:Set ℕ) : ℕ→ℕ := fun x ↦ if x ∈ O then 1 else 0
theorem χsimp {O} : χ O = fun x ↦ if x ∈ O then 1 else 0 := by exact rfl
@[simp] abbrev SetRecursiveIn (O:Set ℕ) (f:ℕ→.ℕ): Prop := Nat.RecursiveIn (χ O) f
@[simp] abbrev SetTuringReducible (A O:Set ℕ) : Prop := Nat.RecursiveIn (χ O) (χ A)
@[simp] abbrev SetTuringReducibleStrict (A O:Set ℕ) : Prop := Nat.RecursiveIn (χ O) (χ A) ∧ ¬ Nat.RecursiveIn (χ A) (χ O)
@[simp] abbrev SetTuringEquivalent (O A:Set ℕ) : Prop := AntisymmRel SetTuringReducible O A
@[simp] noncomputable def evalSet (O:Set ℕ) : Nat.RecursiveIn.Code → ℕ→.ℕ := eval (χ O)
@[simp] noncomputable def evalSet₁ (O:Set ℕ) : ℕ→.ℕ := eval₁ (χ O)
def SetK0 (A:Set ℕ) := {ex:ℕ | (evalSet A ex.unpair.1 ex.unpair.2).Dom}
def SetK (A:Set ℕ) := {x:ℕ | (evalSet A x x).Dom}
abbrev SetJump := SetK
def jumpn : ℕ → Set ℕ → Set ℕ
| 0 => id
| i+1 => SetJump ∘ jumpn i

-- from TuringDegree.lean
protected theorem SetTuringReducible.refl (A:Set ℕ) : SetTuringReducible A A := by exact Nat.RecursiveIn.oracle
protected theorem SetTuringReducible.rfl (A:Set ℕ) : SetTuringReducible A A := SetTuringReducible.refl _
instance : IsRefl (Set ℕ) SetTuringReducible where refl _ := by (expose_names; exact SetTuringReducible.refl x)
theorem SetTuringReducible.trans {A B C:Set ℕ} (hg : SetTuringReducible A B) (hh : SetTuringReducible B C) : SetTuringReducible A C := by
  simp only [SetTuringReducible, SetRecursiveIn] at *
  exact TuringReducible.trans hg hh
instance : IsTrans (Set ℕ) SetTuringReducible := ⟨@SetTuringReducible.trans⟩
instance : IsPreorder (Set ℕ) SetTuringReducible where refl := .refl
theorem SetTuringEquivalent.equivalence : Equivalence SetTuringEquivalent := (AntisymmRel.setoid _ _).iseqv
@[refl] protected theorem SetTuringEquivalent.refl (f : Set ℕ) : SetTuringEquivalent f f := Equivalence.refl equivalence f
@[symm] theorem SetTuringEquivalent.symm {f g : Set ℕ} (h : SetTuringEquivalent f g) : SetTuringEquivalent g f := Equivalence.symm equivalence h
@[trans] theorem SetTuringEquivalent.trans (f g h : Set ℕ) (h₁ : SetTuringEquivalent f g) (h₂ : SetTuringEquivalent g h) : SetTuringEquivalent f h := Equivalence.trans equivalence h₁ h₂
instance : IsPreorder (Set ℕ) SetTuringReducible where refl := SetTuringReducible.refl ; trans := @SetTuringReducible.trans
-- Turing degrees are the equivalence classes of sets of naturals under Turing equivalence.
abbrev TuringDegree := Antisymmetrization (Set ℕ) SetTuringReducible
private instance : Preorder (Set ℕ) where
  le := SetTuringReducible
  le_refl := .refl
  le_trans _ _ _ := SetTuringReducible.trans
  lt := SetTuringReducibleStrict
instance TuringDegree.PO : PartialOrder TuringDegree := instPartialOrderAntisymmetrization
notation:100 A"⌜" => SetJump A
@[reducible,simp] def SetTuringDegreeLE (A B : Set ℕ) : Prop := TuringDegree.PO.le ⟦A⟧ ⟦B⟧
@[reducible,simp] def SetTuringDegreeLT (A B : Set ℕ) : Prop := TuringDegree.PO.lt ⟦A⟧ ⟦B⟧
@[reducible,simp] def SetTuringDegreeEQ (A B : Set ℕ) : Prop := AntisymmRel TuringDegree.PO.le ⟦A⟧ ⟦B⟧
@[reducible,simp] scoped[Computability] infix:50 " ≤ᵀ " => SetTuringDegreeLE
@[reducible,simp] scoped[Computability] infix:50 " <ᵀ " => SetTuringDegreeLT
@[reducible,simp] scoped[Computability] infix:50 " ≡ᵀ " => SetTuringDegreeEQ

section evalSettheorems
theorem exists_code_for_evalSet_nat (O:Set ℕ) (f:ℕ→.ℕ) : SetRecursiveIn O f ↔ ∃ c:ℕ, evalSet O c = f := by exact exists_code_nat (χ O) f
private theorem exists_code_for_evalSet₁ : ∃ c:ℕ, evalSet O c = evalSet₁ O := by apply ((exists_code_for_evalSet_nat O (evalSet₁ O)).mp) rec_eval₁
noncomputable def evalSet₁_code (O:Set ℕ) : ℕ := choose (@exists_code_for_evalSet₁ O)
@[simp] theorem evalSet₁_code_prop : evalSet O (evalSet₁_code O) = evalSet₁ O := by exact choose_spec exists_code_for_evalSet₁
@[simp] theorem evalSet₁_code_prop2 : eval (χ O) (evalSet₁_code O) = evalSet₁ O := by exact choose_spec exists_code_for_evalSet₁

private theorem exists_code_for_eval₁ : ∃ c:ℕ, eval O c = eval₁ O := by apply ((exists_code_nat O (eval₁ O)).mp) rec_eval₁
noncomputable def eval₁_code (O:ℕ→ℕ) : ℕ := choose (@exists_code_for_eval₁ O)
@[simp] theorem eval₁_code_prop : eval O (eval₁_code O) = eval₁ O := by exact choose_spec exists_code_for_eval₁
-- @[simp] theorem eval₁_code_prop2 : eval (χ O) (eval₁_code O) = eval₁ O := by exact choose_spec exists_code_for_eval₁
end evalSettheorems

-- lemmas
lemma χ_eq_0or1 : (χ O x = 0) ∨ (χ O x = 1) := by
  rw [χsimp]
  cases Classical.em (x ∈ O) with
  | inl h => simp only [h, ↓reduceIte, one_ne_zero, or_true]
  | inr h => simp only [h, ↓reduceIte, zero_ne_one, or_false]
lemma some_comp_simp (a:Part ℕ) {f:ℕ→ℕ} {h:a.Dom}:  (Part.some (f (a.get h)) = a >>= (f:ℕ→.ℕ)) := by
  simp only [bind]
  rw [Part.bind]
  exact Eq.symm (Part.assert_pos h)

section SetJumpTheorems
theorem χ_leq_χK0 {O:Set ℕ} : Nat.RecursiveIn (χ (SetK0 O)) (χ O) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl

  let g := fun x => if (χ O) x = 0 then Part.none else Part.some 0

  have hg : Nat.RecursiveIn (χ O) g := by exact Nat.RecursiveIn.ite Nat.RecursiveIn.oracle Nat.RecursiveIn.none Nat.RecursiveIn.zero

  have exists_index_for_g : ∃ c : ℕ, eval (χ O) c = g := by exact (exists_code_nat (χ O) g).mp hg
  rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

  let f':ℕ→.ℕ := fun x => χK0 (Nat.pair index_g x)

  have f_eq_f': (χ O) = f' := by
      simp only [f']
      funext xs
      simp only [χK0]
      simp only [PFun.coe_val, Nat.unpair_pair, Part.coe_some, Part.some_inj]
      rw [index_g_is_g]
      simp only [g]

      cases Classical.em (χ O xs = 0) with
      | inl h => simp [h]
      | inr h =>
        simp only [h]
        simp only [↓reduceIte, Part.some_dom]
        cases χ_eq_0or1
        · (expose_names; exact False.elim (h h_1))
        · (expose_names; exact h_1)

  have f'_recIn_χK0 : Nat.RecursiveIn (χK0) f' := by
    simp only [f']
    refine Nat.RecursiveIn.someTotal (↑χK0) (fun x ↦ χK0 (Nat.pair index_g x)) ?_
    refine Nat.RecursiveIn.totalComp' ?_ ?_
    · exact Nat.RecursiveIn.oracle
    · apply Nat.RecursiveIn.of_primrec Nat.Primrec.pair_proj

  rw [h0]
  rw [f_eq_f']
  exact f'_recIn_χK0
theorem χK0_leq_K0χ {O:Set ℕ} : Nat.RecursiveIn (K0 (χ O)) (χ (SetK0 O)) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl

  let construction := Nat.flatten ∘ K0 (χ O)
  have construction_eq_goal : χK0 = construction := by
    funext xs
    simp only [construction, χK0]
    simp only [Function.comp_apply, Nat.flatten, jump.eq_1, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, ite_not]
  have construction_constructible : Nat.RecursiveIn (K0 (χ O)) construction := by
    simp only [construction]
    exact Nat.RecursiveIn.totalComp (Nat.RecursiveIn.of_primrec Nat.Primrec.flatten) Nat.RecursiveIn.oracle

  rw [h0]
  rw [construction_eq_goal]
  exact construction_constructible
theorem K0χ_leq_χK0 {O:Set ℕ} : Nat.RecursiveIn (χ (SetK0 O)) (K0 (χ O)) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl
  have h1 (ex:ℕ) : (χK0 ex = 0) = ¬(eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  have h2 (ex:ℕ) : ¬χK0 ex = 0 = (eval (χ O) (decodeCode (Nat.unpair ex).1) (Nat.unpair ex).2).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]

  have h3 : (jump (χ O) : ℕ→.ℕ) = (fun ex => if (χK0 ex = 0) then 0 else (eval (χ O) ex.unpair.1 ex.unpair.2) >>= (Nat.succ:ℕ→.ℕ) :ℕ→.ℕ) := by
    funext xs
    cases Classical.em (χK0 xs = 0) with
    | inl h =>
      simp only [h]
      simp only [↓reduceIte]
      simp only [(h1 xs)] at h
      simp only [PFun.coe_val, jump, h, ↓reduceDIte]
      exact rfl
    | inr h =>
      simp only [h]
      simp only [↓reduceIte]
      rw [χsimp]

      simp only [(h2 xs)] at h
      rw [χsimp] at h
      simp only [PFun.coe_val, jump, Nat.succ_eq_add_one]
      simp only [h]
      simp only [↓reduceDIte]

      apply some_comp_simp

  have h5 : Nat.RecursiveIn (χ O) (fun n ↦ eval (↑(χ O)) (decodeCode (Nat.unpair n).1) (Nat.unpair n).2) := by
    exact RecursiveIn.nat_iff.mp eval_part

  rw [h0]
  rw [h3]
  apply Nat.RecursiveIn.ite
  · exact Nat.RecursiveIn.oracle
  · exact Nat.RecursiveIn.zero
  · apply Nat.RecursiveIn.comp
    · exact Nat.RecursiveIn.succ
    · apply TuringReducible.trans' h5 χ_leq_χK0
theorem K0χ_eq_χK0 {O:Set ℕ} : (K0 (χ O)) ≡ᵀᶠ (χ (SetK0 O)) := ⟨K0χ_leq_χK0, χK0_leq_K0χ⟩
theorem χK0_eq_K0χ {O:Set ℕ} : (χ (SetK0 O)) ≡ᵀᶠ (K0 (χ O)) := K0χ_eq_χK0.symm
-- the next two theorems are more or less equivalent to some of the above, with minor tweaks.
theorem χ_leq_χK {O:Set ℕ} : Nat.RecursiveIn (χ (SetK O)) (χ O) := by
  let χK : ℕ→ℕ := fun x ↦ if (eval (χ O) (decodeCode x) x).Dom then 1 else 0
  have h0 : χ (SetK O) = χK := by exact rfl

  -- let compute := (K O) ∘ calculate_specific
  -- let h:ℕ→.ℕ := (compute)

  let g := fun x => if (χ O) x = 0 then Part.none else Part.some 0

  have hg : Nat.RecursiveIn (χ O) g := by exact Nat.RecursiveIn.ite Nat.RecursiveIn.oracle Nat.RecursiveIn.none Nat.RecursiveIn.zero

  have exists_index_for_g : ∃ c : ℕ, eval (χ O) c = g := by exact (exists_code_nat (χ O) g).mp hg
  rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

  let f':ℕ→.ℕ := fun x => χK (calculate_specific $ Nat.pair index_g x)

  have f_eq_f': (χ O) = f' := by
    simp only [f']
    funext xs
    simp only [χK, eval_calculate_specific]
    rw [index_g_is_g]
    simp only [g]

    cases Classical.em (χ O xs = 0) with
    | inl h => simp [h]
    | inr h =>
      simp [h]
      cases χ_eq_0or1
      · (expose_names; exact False.elim (h h_1))
      · (expose_names; exact h_1)

  have f'_recIn_χK : Nat.RecursiveIn (χK) f' := by
    simp only [f']
    refine Nat.RecursiveIn.someTotal (↑χK) (fun x ↦ χK (calculate_specific (Nat.pair index_g x))) ?_
    refine Nat.RecursiveIn.totalComp' ?_ ?_
    · exact Nat.RecursiveIn.oracle
    · refine Nat.RecursiveIn.totalComp' ?_ ?_
      · apply Nat.RecursiveIn.of_primrecIn prim_calculate_specific
      · apply Nat.RecursiveIn.of_primrec Nat.Primrec.pair_proj

  rw [h0]
  rw [f_eq_f']
  exact f'_recIn_χK
theorem Kχ_leq_χK {O:Set ℕ} : Nat.RecursiveIn (χ (SetK O)) (K (χ O)) := by
  let χK : ℕ→ℕ := fun x ↦ if (eval (χ O) (decodeCode x) x).Dom then 1 else 0
  have h0 : χ (SetK O) = χK := by exact rfl
  have h1 (x:ℕ) : (χK x = 0) = ¬(eval (χ O) (decodeCode x) x).Dom := by
    simp only [χK]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  have h2 (x:ℕ) : ¬χK x = 0 = (eval (χ O) (decodeCode x) x).Dom := by
    simp only [χK]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]

  have h3 : (K (χ O) : ℕ→.ℕ) = (fun x => if (χK x = 0) then 0 else (eval (χ O) x x) >>= (Nat.succ:ℕ→.ℕ) :ℕ→.ℕ) := by
    funext xs
    cases Classical.em (χK xs = 0) with
    | inl h =>
      simp only [h]
      simp only [↓reduceIte]
      simp only [(h1 xs)] at h
      simp only [PFun.coe_val, K, h, ↓reduceDIte]
      exact rfl
    | inr h =>
      simp only [h]
      simp only [↓reduceIte]
      rw [χsimp]
      simp only [(h2 xs)] at h
      rw [χsimp] at h
      simp only [PFun.coe_val, K, h, ↓reduceDIte, Nat.succ_eq_add_one, Part.bind_eq_bind]
      apply some_comp_simp

  have h5 : Nat.RecursiveIn (χ O) (fun x ↦ eval (↑(χ O)) (decodeCode x) x) := by
    apply Nat.RecursiveIn.eval_K_computable

  rw [h0]
  rw [h3]
  apply Nat.RecursiveIn.ite
  · exact Nat.RecursiveIn.oracle
  · exact Nat.RecursiveIn.zero
  · apply Nat.RecursiveIn.comp
    · exact Nat.RecursiveIn.succ
    · apply TuringReducible.trans' h5 χ_leq_χK
theorem χK_leq_χK0 {O:Set ℕ} : Nat.RecursiveIn (χ (SetK0 O)) (χ (SetK O)) := by
  have main : (χ (SetK O)) = (χ (SetK0 O)) ∘ fun x=> Nat.pair x x := by
    funext xs
    simp only [χ, SetK, Set.mem_setOf_eq, SetK0, Function.comp_apply, Nat.unpair_pair]
  rw [main]
  exact Nat.RecursiveIn.totalComp Nat.RecursiveIn.oracle (Nat.RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id))
theorem Kχ_eq_χK {O:Set ℕ} : (χ (SetK O)) ≡ᵀᶠ (K (χ O)) := by
  constructor
  · apply TuringReducible.trans (χK_leq_χK0)
    apply TuringReducible.trans (χK0_leq_K0χ)
    apply TuringReducible.trans (K0_leq_K (χ O))
    exact Nat.RecursiveIn.oracle
  · exact Kχ_leq_χK

-- why does the below fail?
-- #check K0_eq_K.le

theorem χK0_eq_χK {O:Set ℕ} : (χ (SetK0 O)) ≡ᵀᶠ (χ (SetK O)) := by
  apply TuringEquivalent.trans
  · exact χK0_eq_K0χ
  · apply TuringEquivalent.trans
    · exact K0_eq_K.symm
    · exact Kχ_eq_χK.symm
theorem SetK0_eq_SetK {O:Set ℕ} : (SetK0 O) ≡ᵀ (SetK O) := by
  constructor
  · exact χK0_eq_χK.le
  · exact χK0_eq_χK.ge
theorem Set_leq_SetK {O:Set ℕ} : O ≤ᵀ (SetK O) := χ_leq_χK

theorem SetJump_not_leq_Set {O:Set ℕ} : ¬O⌜≤ᵀO := by
  intro h
  simp only [SetJump] at h
  apply TuringReducible.trans (Kχ_leq_χK) at h
  apply K_not_leq_f
  exact h
theorem Set_lt_SetJump {O:Set ℕ} : O<ᵀO⌜ := by
  constructor
  · exact Set_leq_SetK
  · exact SetJump_not_leq_Set
end SetJumpTheorems


/-- `W O e` := domain of e^th oracle program -/
abbrev W (O:Set ℕ) (e : ℕ) := (evalSet O e).Dom
/-- `WR O e` := range of e^th oracle program -/
abbrev WR (O:Set ℕ) (e : ℕ) := (evalSet O e).ran

-- noncomputable def eval_ef (O:Set ℕ): ℕ→.ℕ := fun ex => Nat.pair <$> ex <*> evalSet₁ O ex
-- def eval_first (O:ℕ→ℕ) (x:ℕ) : ℕ→ℕ→.ℕ := fun ab => (eval O x ab.unpair.1) >>= (fun index => (Nat.pair index ab.unpair.2))  >>= fun ex => (eval₁ O ex)
-- def code_id:ℕ:= (Nat.RecursiveIn.Code.id)
-- #eval code_id
def code_to_code_ef:ℕ→ℕ:=fun c=>(pair Nat.RecursiveIn.Code.id c)
theorem code_ef_left (h:(eval O c x).Dom) : eval O (left.comp $ code_to_code_ef c) x = x := by
  have h0 : (eval O c x).get h ∈ (eval O c x) := by exact Part.get_mem h
  have h1 : eval O c x = Part.some ((eval O c x).get h) := by exact Part.get_eq_iff_eq_some.mp rfl

  simp [code_to_code_ef, eval]
  rw [h1]
  -- should maybe define some theorem that simplfies the Nat.pair <*> business
  simp [Seq.seq]
  exact Part.Dom.bind h fun y ↦ Part.some x
theorem eval_code_ef : eval O (code_to_code_ef c) x = Nat.pair <$> x <*> (eval O c x) := by
  simp [code_to_code_ef,eval]
theorem code_ef_dom_iff_code_dom : (eval O (code_to_code_ef c) x).Dom ↔ (eval O c x).Dom := by
  constructor
  · contrapose
    simp [code_to_code_ef]
    intro h
    simp [eval]
    simp [Seq.seq]
    exact h
  · simp [code_to_code_ef]
    intro h
    simp [eval]
    simp [Seq.seq]
    exact h



-- private def dom_to_ran_helper : (ℕ→ℕ) :=
/-- Given a code `e`, returns a code whose range is the domain of `e`. -/
noncomputable def dom_to_ran {O:Set ℕ} : (ℕ→ℕ) := fun e => curry ((comp) (right.comp left) (code_to_code_ef (evalSet₁_code O))) e
-- dom_to_ran(e) is the function which takes on input `x`, runs `[e](x)`, then binds to `const x`.
-- `[dom_to_ran(e)](x)=[(const x) ∘ eval ∘ (pair e x)]`

theorem dom_to_ran_prop : (W O e) = (WR O (@dom_to_ran O e)) := by
  ext xs
  constructor
  · intro h
    simp at h
    rcases h with ⟨y,hy⟩
    simp [WR]
    simp only [dom_to_ran]
    simp only [decodeCode_encodeCode]
    have h0 : (eval (χ O) e xs).Dom := by
      apply Part.dom_iff_mem.mpr
      exact Exists.intro y hy
    have h5234 : (eval (χ O) (decodeCode (evalSet₁_code O)) (Nat.pair e xs)).Dom := by
      rw [evalSet₁_code_prop2]
      simp [evalSet₁]
      exact h0


    rw [PFun.ran]
    simp only [eval_curry, Set.mem_setOf_eq]
    use xs
    simp only [eval, Part.coe_some, Part.bind_eq_bind]
    rw [eval_code_ef]

    apply Part.dom_iff_mem.mp at h5234
    rcases h5234 with ⟨y',hy'⟩
    apply Part.eq_some_iff.mpr at hy'
    rw [hy']

    simp [Seq.seq]

  · contrapose
    intro h
    simp at h
    -- rcases h with ⟨y,hy⟩
    simp [WR]
    simp only [dom_to_ran]
    simp only [decodeCode_encodeCode]
    have h0 : ¬(eval (χ O) e xs).Dom := by
      refine Part.eq_none_iff'.mp ?_
      exact Part.eq_none_iff.mpr h
    have h5234 : ¬(eval (χ O) (decodeCode (evalSet₁_code O)) (Nat.pair e xs)).Dom := by
      rw [evalSet₁_code_prop2]
      simp [evalSet₁]
      exact h0

    rw [PFun.ran]
    simp only [eval_curry, Set.mem_setOf_eq]
    simp
    intro x
    simp only [eval, Part.coe_some, Part.bind_eq_bind]
    rw [eval_code_ef]

    cases Classical.em ((eval (χ O) (decodeCode (evalSet₁_code O)) (Nat.pair e x)).Dom) with
    | inl h' =>
      have h123: ¬ x=xs  := by
        intro hxx
        rw [hxx] at h'
        contradiction
      apply Part.dom_iff_mem.mp at h'
      rcases h' with ⟨y',hy'⟩
      apply Part.eq_some_iff.mpr at hy'
      rw [hy']
      simp [Seq.seq]
      exact fun a ↦ h123 (id (Eq.symm a))
    | inr h' =>
      apply Part.eq_none_iff'.mpr at h'
      rw [h']
      simp [Seq.seq]


theorem Nat.Primrec.dom_to_ran' : Nat.Primrec dom_to_ran := by sorry

def dovetail {h:Nat.RecursiveIn O f} : ℕ→ℕ := fun x => 0
/--
Given a code "e", dovetail_code e gives the code to the function which, on input n:

runs [e](0) for 1 step (i.e. evalnO e 0 1)

runs [e](0) for 2 steps
runs [e](1) for 1 step

runs [e](0) for 3 steps
runs [e](1) for 2 steps
runs [e](2) for 1 step

...

until it finds the n^th input to [e] that halts.
-/
def dovetail_code (e:ℕ) : ℕ := 0
theorem dovetail_code_total : (eval O (dovetail_code e)).Dom = ℕ := by sorry
-- theorem dovetail_eq : eval O (dovetail_code e) ≡ᵀᶠ eval O e := by sorry

def PFun.nat_graph (f : ℕ→.ℕ) : Set ℕ := { xy | xy.unpair.2 ∈ f xy.unpair.1 }
def total_graph (f : ℕ → ℕ) : Set ℕ := { xy | xy.unpair.2 = f xy.unpair.1 }
theorem partfun_eq_χgraph {f:ℕ→ℕ} : f ≡ᵀᶠ χ (total_graph f) := by sorry



-- CE O A means that A is c.e. in O.
def CE (O:Set ℕ) (A:Set ℕ) : Prop := ∃ c:ℕ, A = W O c
theorem CE_range : CE O A ↔ ∃ c:ℕ, A = WR O c := by sorry

theorem Computable_iff_CE_compCE : A≤ᵀB ↔ (CE B A ∧ CE B Aᶜ) := by sorry

-- immune O A := A is immune in O
def immune (O:Set ℕ) (A:Set ℕ) : Prop := (A.Infinite) ∧ (∀c:ℕ, (W O c).Infinite → ¬(W O c ⊆ A))
-- simple O A := A is simple in O
def simple (O:Set ℕ) (A:Set ℕ) : Prop := (CE O A) ∧ immune O Aᶜ
theorem simple_above_empty (h:simple ∅ A): ∅<ᵀA := by sorry

theorem exists_simple_set : ∃ A:Set ℕ, simple O A := by
  sorry



-- in cooper p.220 theres the requirement also that A≤ᵀjumpn 1 ∅. is this necessary?
def low (n:ℕ) (A:Set ℕ) : Prop := jumpn n A = jumpn n ∅

theorem low_below_K (h:low 1 A) : A<ᵀ∅⌜ := by
  simp [low, jumpn] at h
  have h0 : A⌜≡ᵀ∅⌜ := by exact Eq.antisymmRel (congrArg (toAntisymmetrization SetTuringReducible) h)
  have h1 : A<ᵀA⌜ := by exact Set_lt_SetJump
  exact lt_of_lt_of_eq h1 (congrArg (toAntisymmetrization SetTuringReducible) h)

theorem exists_low_simple_set : ∃ A:Set ℕ, simple ∅ A ∧ low 1 A := by
  sorry

theorem posts_problem_solution : ∃ A:Set ℕ, ∅<ᵀA ∧ A<ᵀ∅⌜ := by
  rcases exists_low_simple_set with ⟨A,hA⟩
  use A
  have ⟨h0,h1⟩ := hA
  constructor
  · exact simple_above_empty h0
  · exact low_below_K h1
