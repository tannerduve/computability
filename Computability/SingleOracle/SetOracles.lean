import Computability.SingleOracle.Jump

open Classical

-- definitions
noncomputable def χ (O:Set ℕ) : ℕ→ℕ := fun x ↦ if x ∈ O then 1 else 0
theorem χsimp {O} : χ O = fun x ↦ if x ∈ O then 1 else 0 := by exact rfl
def SetRecursiveIn (O A:Set ℕ): Prop := RecursiveIn (χ O) (χ A)
abbrev SetTuringReducible (O A:Set ℕ) : Prop := SetRecursiveIn O A
abbrev SetTuringEquivalent (O A:Set ℕ) : Prop := AntisymmRel SetTuringReducible O A
noncomputable def evaloSet (O : Set ℕ) : codeo → ℕ →. ℕ := evalo (fun x => if x∈O then 1 else 0:ℕ→ℕ)
def SetK0 (A:Set ℕ) := {ex:ℕ | (evaloSet A ex.unpair.1 ex.unpair.2).Dom}
def SetK (A:Set ℕ) := {x:ℕ | (evaloSet A x x).Dom}



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

theorem K0χ_eq_χK0 {O:Set ℕ} : TuringEquivalent (K0 (χ O)) (χ (SetK0 O)) := ⟨K0χ_leq_χK0, χK0_leq_K0χ⟩
theorem χK0_eq_K0χ {O:Set ℕ} : TuringEquivalent (χ (SetK0 O)) (K0 (χ O)) := K0χ_eq_χK0.symm


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

theorem Kχ_eq_χK {O:Set ℕ} : TuringEquivalent (χ (SetK O)) (K (χ O)) := by
  constructor
  · apply TuringReducible.trans (χK_leq_χK0)
    apply TuringReducible.trans (K0χ_eq_χK0.ge)
    apply TuringReducible.trans (K0_eq_K.ge)
    exact RecursiveIn.oracle
  · exact Kχ_leq_χK


theorem χK0_eq_χK {O:Set ℕ} : TuringEquivalent (χ (SetK0 O)) (χ (SetK O)) := by
  apply TuringEquivalent.trans
  · exact χK0_eq_K0χ
  · apply TuringEquivalent.trans
    · exact K0_eq_K.symm
    · exact Kχ_eq_χK.symm

theorem SetK0_eq_SetK {O:Set ℕ} : SetTuringEquivalent (SetK0 O) (SetK O) := by
  simp only [SetTuringEquivalent]

  constructor
  · simp only [SetTuringReducible, SetRecursiveIn]
    exact χK0_eq_χK.ge
  · simp only [SetTuringReducible, SetRecursiveIn]
    exact χK0_eq_χK.le


  -- rw [SetTuringReducible]



  -- have h : χ (SetK0 O) = fun x ↦ if (evalo (fun x ↦ if x ∈ O then 1 else 0) (decodeCodeo (Nat.unpair x).1) (Nat.unpair x).2).Dom then 1 else 0 := by
  --   simp [SetK0]
  -- simp [jump]
  -- simp [ite_not]
  -- sorry

-- theorem SetK0_leq_K : SetTuringReducible (SetK0 O) (SetK O) := by
--   rw [SetK0, SetK, evaloSet]
--   simp [SetRecursiveIn]

  -- let χ_K0 := fun x ↦
  --   if (evalo (fun x ↦ if x ∈ O then 1 else 0) (decodeCodeo (Nat.unpair x).1) (Nat.unpair x).2).Dom then 1 else 0
  -- have h : (χ_K0) = (Nat.flatten) ∘ (jump (fun x ↦ if x ∈ O then 1 else 0)) := by
  --   simp only [χ_K0]
  --   funext xs
  --   simp only [Function.comp_apply, Nat.flatten, jump, Nat.succ_eq_add_one, dite_eq_right_iff, Nat.add_eq_zero, one_ne_zero, and_false, imp_false, ite_not]



    -- simp only [jump]



-- theorem SetK0eqK : SetTuringEquivalent (SetK0 O) (SetK O) := by
--   rw [SetK0, SetK]
--   constructor
--   exact?
