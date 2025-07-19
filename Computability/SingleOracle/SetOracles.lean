import Computability.SingleOracle.Jump
import Mathlib.Order.Basic

open scoped Computability
open Classical

-- definitions
noncomputable def χ (O:Set ℕ) : ℕ→ℕ := fun x ↦ if x ∈ O then 1 else 0
theorem χsimp {O} : χ O = fun x ↦ if x ∈ O then 1 else 0 := by exact rfl
def SetRecursiveIn (O A:Set ℕ): Prop := RecursiveIn (χ O) (χ A)
@[simp] abbrev SetTuringReducible (A O:Set ℕ) : Prop := SetRecursiveIn O A
@[simp] abbrev SetTuringReducibleStrict (A O:Set ℕ) : Prop := SetRecursiveIn O A ∧ ¬ SetRecursiveIn A O
@[simp] abbrev SetTuringEquivalent (O A:Set ℕ) : Prop := AntisymmRel SetTuringReducible O A
noncomputable def evaloSet (O : Set ℕ) : codeo → ℕ →. ℕ := evalo (fun x => if x∈O then 1 else 0:ℕ→ℕ)
def SetK0 (A:Set ℕ) := {ex:ℕ | (evaloSet A ex.unpair.1 ex.unpair.2).Dom}
def SetK (A:Set ℕ) := {x:ℕ | (evaloSet A x x).Dom}
abbrev SetJump := SetK
def jumpn : ℕ → Set ℕ → Set ℕ
| 0 => id
| i+1 => SetJump ∘ jumpn i

-- from TuringDegree.lean
protected theorem SetTuringReducible.refl (A:Set ℕ) : SetTuringReducible A A := by exact RecursiveIn.oracle
protected theorem SetTuringReducible.rfl (A:Set ℕ) : SetTuringReducible A A := SetTuringReducible.refl _
instance : IsRefl (Set ℕ) SetTuringReducible where refl _ := by (expose_names; exact SetTuringReducible.refl x)
theorem SetTuringReducible.trans {A B C:Set ℕ} (hg : SetTuringReducible A B) (hh : SetTuringReducible B C) : SetTuringReducible A C := by sorry

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
instance TuringDegree.instPartialOrder : PartialOrder TuringDegree :=
  instPartialOrderAntisymmetrization
notation:100 A"⌜" => SetJump A
-- @[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => SetTuringReducible
-- @[inherit_doc] scoped[Computability] infix:50 " <ᵀ " => SetTuringReducibleStrict
-- @[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => SetTuringEquivalent
-- scoped[Computability] infix:50 " ≤ᵀ " => fun x y => TuringDegree.instPartialOrder.le (toAntisymmetrization SetTuringReducible x) (toAntisymmetrization SetTuringReducible y)
scoped[Computability] infix:50 " ≤ᵀ " => fun x y => TuringDegree.instPartialOrder.le ⟦x⟧ ⟦y⟧
scoped[Computability] infix:50 " <ᵀ " => fun x y => TuringDegree.instPartialOrder.lt ⟦x⟧ ⟦y⟧
scoped[Computability] infix:50 " ≡ᵀ " => fun x y => AntisymmRel TuringDegree.instPartialOrder.le ⟦x⟧ ⟦y⟧

-- #check (∅ ≤ᵀ (SetK ∅))
#check (toAntisymmetrization SetTuringReducible (∅:Set ℕ))


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

-- theorems

theorem χ_leq_χK0 {O:Set ℕ} : RecursiveIn (χ (SetK0 O)) (χ O) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl

  let g := fun x => if (χ O) x = 0 then Part.none else Part.some 0

  have hg : RecursiveIn (χ O) g := by exact RecursiveIn.ite RecursiveIn.oracle RecursiveIn.none RecursiveIn.zero

  have exists_index_for_g : ∃ c : ℕ, evalo (χ O) c = g := by exact (exists_codeN_rel (χ O) g).mp hg
  rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

  let f':ℕ→.ℕ := fun x => χK0 (Nat.pair index_g x)

  have f_eq_f': (χ O) = f' := by
      simp only [f']
      funext xs
      simp [χK0]
      rw [index_g_is_g]
      simp [g]

      cases Classical.em (χ O xs = 0) with
      | inl h => simp [h]
      | inr h =>
        simp [h]
        cases χ_eq_0or1
        · (expose_names; exact False.elim (h h_1))
        · (expose_names; exact h_1)


  -- i dont need f'_recIn_χ... i proved it accidentally.
  have f'_recIn_χ : RecursiveIn (χ O) f' := by
    simp [f', χK0, index_g_is_g, g]
    rw [χsimp]
    simp
    have intermediate : (fun x ↦ Part.some (if (if x ∈ O then Part.some 0 else Part.none).Dom then 1 else 0)) = (χ O : ℕ→.ℕ):= by
      funext xs
      cases Classical.em (xs ∈ O) with
      | inl h => simp [h, χ]
      | inr h => simp [h, χ]
    rw [intermediate]
    apply RecursiveIn.oracle

  have f'_recIn_χK0 : RecursiveIn (χK0) f' := by
    simp [f']
    refine RecursiveIn.someTotal (↑χK0) (fun x ↦ χK0 (Nat.pair index_g x)) ?_
    refine RecursiveIn.totalComp' ?_ ?_
    · exact RecursiveIn.oracle
    · apply RecursiveIn.of_primrec Nat.Primrec.pair_proj

  rw [h0]
  rw [f_eq_f']
  exact f'_recIn_χK0

theorem χK0_leq_K0χ {O:Set ℕ} : RecursiveIn (K0 (χ O)) (χ (SetK0 O)) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl

  let construction := Nat.flatten ∘ K0 (χ O)
  have construction_eq_goal : χK0 = construction := by
    funext xs
    simp [construction, χK0]
  have construction_constructible : RecursiveIn (K0 (χ O)) construction := by
    simp [construction]
    exact RecursiveIn.totalComp (RecursiveIn.of_primrec Nat.Primrec.flatten) RecursiveIn.oracle

  rw [h0]
  rw [construction_eq_goal]
  exact construction_constructible

theorem K0χ_leq_χK0 {O:Set ℕ} : RecursiveIn (χ (SetK0 O)) (K0 (χ O)) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by exact rfl
  have h1 (ex:ℕ) : (χK0 ex = 0) = ¬(evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  have h2 (ex:ℕ) : ¬χK0 ex = 0 = (evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]

  have h3 : (jump (χ O) : ℕ→.ℕ) = (fun ex => if (χK0 ex = 0) then 0 else (evalo (χ O) ex.unpair.1 ex.unpair.2) >>= (Nat.succ:ℕ→.ℕ) :ℕ→.ℕ) := by
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

  have h5 : RecursiveIn (χ O) (fun n ↦ evalo (↑(χ O)) (decodeCodeo (Nat.unpair n).1) (Nat.unpair n).2) := by
    exact RecursiveIn.evalo_computable

  rw [h0]
  rw [h3]
  apply RecursiveIn.ite
  · exact RecursiveIn.oracle
  · exact RecursiveIn.zero
  · apply RecursiveIn.comp
    · exact RecursiveIn.succ
    · apply TuringReducible.trans h5 χ_leq_χK0

theorem K0χ_eq_χK0 {O:Set ℕ} : (K0 (χ O)) ≡ᵀ (χ (SetK0 O)) := ⟨K0χ_leq_χK0, χK0_leq_K0χ⟩
theorem χK0_eq_K0χ {O:Set ℕ} : (χ (SetK0 O)) ≡ᵀ (K0 (χ O)) := K0χ_eq_χK0.symm


-- the next two theorems are more or less equivalent to some of the above, with minor tweaks.
theorem χ_leq_χK {O:Set ℕ} : RecursiveIn (χ (SetK O)) (χ O) := by
  let χK : ℕ→ℕ := fun x ↦ if (evalo (χ O) (decodeCodeo x) x).Dom then 1 else 0
  have h0 : χ (SetK O) = χK := by exact rfl

  -- let compute := (K O) ∘ codeo_calculate
  -- let h:ℕ→.ℕ := (compute)

  let g := fun x => if (χ O) x = 0 then Part.none else Part.some 0

  have hg : RecursiveIn (χ O) g := by exact RecursiveIn.ite RecursiveIn.oracle RecursiveIn.none RecursiveIn.zero

  have exists_index_for_g : ∃ c : ℕ, evalo (χ O) c = g := by exact (exists_codeN_rel (χ O) g).mp hg
  rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

  let f':ℕ→.ℕ := fun x => χK (codeo_calculate $ Nat.pair index_g x)

  have f_eq_f': (χ O) = f' := by
    simp only [f']
    funext xs
    simp [χK]
    simp [codeo_calculate']
    rw [index_g_is_g]
    simp [g]

    cases Classical.em (χ O xs = 0) with
    | inl h => simp [h]
    | inr h =>
      simp [h]
      cases χ_eq_0or1
      · (expose_names; exact False.elim (h h_1))
      · (expose_names; exact h_1)

  have f'_recIn_χK : RecursiveIn (χK) f' := by
    simp [f']
    refine RecursiveIn.someTotal (↑χK) (fun x ↦ χK (codeo_calculate (Nat.pair index_g x))) ?_
    refine RecursiveIn.totalComp' ?_ ?_
    · exact RecursiveIn.oracle
    · refine RecursiveIn.totalComp' ?_ ?_
      · apply RecursiveIn.of_primrec Primrec.codeo_calculate
      · apply RecursiveIn.of_primrec Nat.Primrec.pair_proj

  rw [h0]
  rw [f_eq_f']
  exact f'_recIn_χK

theorem Kχ_leq_χK {O:Set ℕ} : RecursiveIn (χ (SetK O)) (K (χ O)) := by
  let χK : ℕ→ℕ := fun x ↦ if (evalo (χ O) (decodeCodeo x) x).Dom then 1 else 0
  have h0 : χ (SetK O) = χK := by exact rfl
  have h1 (x:ℕ) : (χK x = 0) = ¬(evalo (χ O) (decodeCodeo x) x).Dom := by
    simp only [χK]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  have h2 (x:ℕ) : ¬χK x = 0 = (evalo (χ O) (decodeCodeo x) x).Dom := by
    simp only [χK]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]

  have h3 : (K (χ O) : ℕ→.ℕ) = (fun x => if (χK x = 0) then 0 else (evalo (χ O) x x) >>= (Nat.succ:ℕ→.ℕ) :ℕ→.ℕ) := by
    funext xs
    cases Classical.em (χK xs = 0) with
    | inl h =>
      simp only [h]
      simp only [↓reduceIte]
      simp only [(h1 xs)] at h
      simp [h]
      exact rfl
    | inr h =>
      simp only [h]
      simp only [↓reduceIte]
      rw [χsimp]
      simp only [(h2 xs)] at h
      rw [χsimp] at h
      simp only [PFun.coe_val, K, h, ↓reduceDIte, Nat.succ_eq_add_one, Part.bind_eq_bind]
      apply some_comp_simp

  have h5 : RecursiveIn (χ O) (fun x ↦ evalo (↑(χ O)) (decodeCodeo x) x) := by
    apply RecursiveIn.evalo_K_computable
    -- apply
    -- exact?

  rw [h0]
  rw [h3]
  apply RecursiveIn.ite
  · exact RecursiveIn.oracle
  · exact RecursiveIn.zero
  · apply RecursiveIn.comp
    · exact RecursiveIn.succ
    · apply TuringReducible.trans h5 χ_leq_χK

theorem χK_leq_χK0 {O:Set ℕ} : RecursiveIn (χ (SetK0 O)) (χ (SetK O)) := by
  have main : (χ (SetK O)) = (χ (SetK0 O)) ∘ fun x=> Nat.pair x x := by
    funext xs
    simp [SetK0, SetK, χ]
  rw [main]
  exact RecursiveIn.totalComp RecursiveIn.oracle (RecursiveIn.of_primrec (Nat.Primrec.pair Nat.Primrec.id Nat.Primrec.id))

theorem Kχ_eq_χK {O:Set ℕ} : (χ (SetK O)) ≡ᵀ (K (χ O)) := by
  constructor
  · apply TuringReducible.trans (χK_leq_χK0)
    apply TuringReducible.trans (K0χ_eq_χK0.ge)
    apply TuringReducible.trans (K0_eq_K.ge)
    exact RecursiveIn.oracle
  · exact Kχ_leq_χK


theorem χK0_eq_χK {O:Set ℕ} : (χ (SetK0 O)) ≡ᵀ (χ (SetK O)) := by
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
  apply TuringReducible.trans (Kχ_eq_χK.ge) at h
  apply K_not_leq_f
  exact h
theorem Set_lt_SetJump {O:Set ℕ} : O<ᵀO⌜ := by
  constructor
  · exact Set_leq_SetK
  · exact SetJump_not_leq_Set


-- W O e := domain of e^th oracle program
abbrev W (O : Set ℕ) (e : ℕ) := (evaloSet O e).Dom
-- WR O e := range of e^th oracle program
abbrev WR (O : Set ℕ) (e : ℕ) := (evaloSet O e).ran

def dom_to_ran : (ℕ→ℕ) := fun x => x
theorem dom_to_ran' : SetTuringEquivalent (W O e) (WR O (dom_to_ran e)) := by sorry
theorem Nat.Primrec.dom_to_ran' : Nat.Primrec dom_to_ran := by sorry

def dovetail {h:RecursiveIn O f} : ℕ→ℕ := fun x => 0
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
theorem dovetail_code_total : (evalo O (dovetail_code e)).Dom = ℕ := by sorry
theorem dovetail_eq : evalo O (dovetail_code e) ≡ᵀ evalo O e := by sorry

def PFun.nat_graph (f : ℕ →. ℕ) : Set ℕ := { xy | xy.unpair.2 ∈ f xy.unpair.1 }
def total_graph (f : ℕ → ℕ) : Set ℕ := { xy | xy.unpair.2 = f xy.unpair.1 }
theorem partfun_eq_χgraph {f:ℕ→ℕ} : f ≡ᵀ χ (total_graph f) := by sorry



-- CE O A means that A is c.e. in O.
def CE (O:Set ℕ) (A:Set ℕ) : Prop := ∃ c:ℕ, A = W O c
theorem CE_range : CE O A ↔ ∃ c:ℕ, A = WR O c := by sorry

-- immune O A := A is immune in O
def immune (O:Set ℕ) (A:Set ℕ) : Prop := (A.Infinite) ∧ (∀c:ℕ, (W O c).Infinite → ¬(W O c ⊆ A))
-- simple O A := A is simple in O
def simple (O:Set ℕ) (A:Set ℕ) : Prop := (CE O A) ∧ immune O Aᶜ

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
  sorry
