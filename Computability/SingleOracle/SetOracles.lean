import Computability.SingleOracle.Jump

open Classical

def SetRecursiveIn (O A : Set ℕ): Prop :=
  RecursiveIn (fun x => if x ∈ O then 1 else 0) (fun x => if x ∈ A then 1 else 0)

abbrev SetTuringReducible (O A : Set ℕ) : Prop :=
  SetRecursiveIn O A

abbrev SetTuringEquivalent (O A : Set ℕ) : Prop :=
  AntisymmRel SetTuringReducible O A

noncomputable def evaloSet (O : Set ℕ) : codeo → ℕ →. ℕ := evalo (fun x => if x ∈ O then 1 else 0)

def SetK0 (A : Set ℕ) := {ex : ℕ | (evaloSet A ex.unpair.1 ex.unpair.2).Dom}
def SetK (A : Set ℕ) := {x : ℕ | (evaloSet A x x).Dom}

/--
The characteristic function of a set A evaluated at x is 1 if x ∈ A and 0 otherwise.
-/
noncomputable def χ (O : Set ℕ) : ℕ →. ℕ := fun x ↦ if x ∈ O then 1 else 0

/--
The jump of the characteristic function of a set A is the characteristic function of the set of
programs that halt on input x with oracle A.
-/
theorem jumpχ_recIn_χK0 (O:Set ℕ) : RecursiveIn (χ (SetK0 O)) (jump (χ O)) := by
  let χK0 : ℕ→.ℕ := fun x ↦ if (evalo (fun x ↦ if x ∈ O then 1 else 0) (decodeCodeo (Nat.unpair x).1) (Nat.unpair x).2).Dom then 1 else 0
  have h0 : χ (SetK0 O) = χK0 := by
    simp only [χK0]
    exact rfl
  rw [h0]

  have h1 (ex:ℕ) : (¬χK0 ex = 0) = (evalo (χ O) (decodeCodeo (Nat.unpair ex).1) (Nat.unpair ex).2).Dom := by sorry

  have h2 : jump (χ O) = fun ex => dite (χK0 ex = 0) (λ _ => 0) ((evalo (χ O) ex.unpair.1 ex.unpair.2).get ∘ (h1 ex).mp) := by sorry

  -- have h : χ (SetK0 O) = fun x ↦ if (evalo (fun x ↦ if x ∈ O then 1 else 0) (decodeCodeo (Nat.unpair x).1) (Nat.unpair x).2).Dom then 1 else 0 := by
  --   simp [SetK0]
  -- simp [jump]
  -- simp [ite_not]
  sorry

theorem SetK0_leq_K : SetTuringReducible (SetK0 O) (SetK O) := by
  rw [SetK0, SetK, evaloSet]
  simp [SetRecursiveIn]
  sorry

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
