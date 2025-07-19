import Computability.SingleOracle.Jump

open Classical

def SetRecursiveIn (O A:Set ℕ): Prop :=
  RecursiveIn (fun x => if x∈O then 1 else 0) (fun x => if x∈A then 1 else 0)

abbrev SetTuringReducible (O A:Set ℕ) : Prop :=
  SetRecursiveIn O A

abbrev SetTuringEquivalent (O A:Set ℕ) : Prop :=
  AntisymmRel SetTuringReducible O A

noncomputable def evaloSet (O : Set ℕ) : codeo → ℕ →. ℕ := evalo (fun x => if x∈O then 1 else 0:ℕ→ℕ)

def SetK0 (A:Set ℕ) := {ex:ℕ | (evaloSet A ex.unpair.1 ex.unpair.2).Dom}
def SetK (A:Set ℕ) := {x:ℕ | (evaloSet A x x).Dom}

noncomputable def χ (O:Set ℕ) : ℕ→ℕ := fun x ↦ if x ∈ O then 1 else 0
theorem χsimp : χ O = fun x ↦ if x ∈ O then 1 else 0 := by exact rfl

@[simp] theorem partNat {a:ℕ}: (a:Part ℕ) = Part.some a := by exact rfl

lemma test : ¬((1:Part ℕ) = (0:Part ℕ)) := by
  have test2 : (1:Part ℕ)=Part.some 1 := by exact rfl
  have test3 : (0:Part ℕ)=Part.some 0 := by exact rfl
  simp [test2, test3]
  -- rw [partNat]
  -- simp [partNat]




theorem χ0or1 : (χ O x = 0) ∨ (χ O x = 1) := by
  rw [χsimp]
  cases Classical.em (x ∈ O) with
  | inl h => simp only [h, ↓reduceIte, one_ne_zero, or_true]
  | inr h => simp only [h, ↓reduceIte, zero_ne_one, or_false]

theorem χ_recIn_χK0 {O:Set ℕ} : RecursiveIn (χ (SetK0 O)) (χ O) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by
    simp only [SetK0,evaloSet]
    simp only [χK0]
    rw [χsimp]
    rw [χsimp]
    simp only [Set.mem_setOf_eq]

  let g := fun x => if (χ O) x = 0 then Part.none else Part.some 0

  have hg : RecursiveIn (χ O) g := by exact RecursiveIn.ite RecursiveIn.oracle RecursiveIn.none RecursiveIn.zero


  have exists_index_for_g : ∃ c : ℕ, evalo (χ O) c = g := by exact (exists_codeN_rel (χ O) g).mp hg
  rcases exists_index_for_g with ⟨index_g,index_g_is_g⟩

  -- let compute := (jump f) ∘ (Nat.pair (encodeCodeo (codeo.oracle)));
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
        cases χ0or1
        · (expose_names; exact False.elim (h h_1))
        · (expose_names; exact h_1)


  have f'_recIn_χ : RecursiveIn (χ O) f' := by
    simp [f', χK0, index_g_is_g, g]
    rw [χsimp]
    simp
    -- have intermediate : (fun x ↦ Part.some (if (if x ∈ O then Part.some 0 else Part.none).Dom then 1 else 0)) = ((fun x ↦ if x ∈ O then 1 else 0:ℕ→ℕ):ℕ→.ℕ):= by
    have intermediate : (fun x ↦ Part.some (if (if x ∈ O then Part.some 0 else Part.none).Dom then 1 else 0)) = (χ O : ℕ→.ℕ):= by
      funext xs
      cases Classical.em (xs ∈ O) with
      | inl h => simp [h, χ]
      | inr h => simp [h, χ]
    rw [intermediate]
    -- apply RecursiveIn.some
    -- have inter2 : (fun x ↦ if x ∈ O then 1 else 0 : ℕ→.ℕ) = Part.some ∘ (fun x ↦ if x ∈ O then 1 else 0) := by
    --   funext xs
    --   simp
    -- apply RecursiveIn.totalComp
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


      -- simp
    -- exact?
  -- have compute_recIn_fJump : compute ≤ᵀ (f⌜) := by
  --   apply RecursiveIn.totalComp
  --   · exact RecursiveIn.oracle
  --   · apply RecursiveIn.of_primrec
  --     refine Primrec.nat_iff.mp ?_
  --     apply Primrec.projection
  --     exact Primrec₂.natPair

  -- have f'_recIn_fJump : f' ≤ᵀ (f⌜) := by
  --   simp only [f',TuringReducible]
  --   exact RecursiveIn.jumpDecodeIte compute_recIn_fJump

  -- exact RecursiveIn.of_eq f'_recIn_fJump (congrFun (id (Eq.symm f_eq_f')))


theorem some_comp_simp (a:Part ℕ) {f:ℕ→ℕ} {h:a.Dom}:  (Part.some (f (a.get h)) = a >>= (f:ℕ→.ℕ)) := by
  simp only [bind]
  rw [Part.bind]
  exact Eq.symm (Part.assert_pos h)

theorem jumpχ_recIn_χK0 {O:Set ℕ} : RecursiveIn (χ (SetK0 O)) (jump (χ O)) := by
  let χK0 : ℕ→ℕ := fun ex ↦ if (evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by
    simp only [SetK0,evaloSet]
    simp only [χK0]
    rw [χsimp]
    rw [χsimp]
    simp only [Set.mem_setOf_eq]

  rw [h0]

  have h1 (ex:ℕ) : (χK0 ex = 0) = ¬(evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  have h2 (ex:ℕ) : ¬χK0 ex = 0 = (evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom := by
    simp only [χK0]
    simp only [ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]


  -- have h2 : jump (χ O) = fun ex => dite (χK0 ex = 0) (λ _ => 0) ((evalo (χ O) ex.unpair.1 ex.unpair.2).get ∘ (h1 ex).mp) := by sorry
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

  rw [h3]



  have h5 : RecursiveIn (χ O) (fun n ↦ evalo (↑(χ O)) (decodeCodeo (Nat.unpair n).1) (Nat.unpair n).2) := by
    exact RecursiveIn.evaloRecInO

  apply RecursiveIn.ite
  · exact RecursiveIn.oracle
  · exact RecursiveIn.zero
  · apply RecursiveIn.comp
    · exact RecursiveIn.succ
    · apply TuringReducible.trans h5 χ_recIn_χK0





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
