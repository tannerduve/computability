import Computability.SingleOracle.Oracle2

@[simp] abbrev TuringReducible (f g : ℕ → ℕ) : Prop := Nat.RecursiveIn g f
@[simp] abbrev TuringReducibleStrict (f g : ℕ → ℕ) : Prop := Nat.RecursiveIn g f ∧ ¬ Nat.RecursiveIn f g
@[simp] abbrev TuringEquivalent (f g : ℕ → ℕ) : Prop := AntisymmRel TuringReducible f g

@[reducible,simp,inherit_doc] scoped[Computability] infix:50 " ≤ᵀᶠ " => TuringReducible
@[reducible,simp,inherit_doc] scoped[Computability] infix:50 " ≡ᵀᶠ " => TuringEquivalent
@[reducible,simp,inherit_doc] scoped[Computability] infix:50 " <ᵀᶠ " => TuringReducibleStrict

open scoped Computability

protected theorem TuringReducible.refl (f : ℕ → ℕ) : f ≤ᵀᶠ f := by exact Nat.RecursiveIn.oracle
protected theorem TuringReducible.rfl : f ≤ᵀᶠ f := .refl _

instance : IsRefl (ℕ → ℕ) TuringReducible where refl _ := .rfl

theorem TuringReducible.trans (hg : f ≤ᵀᶠ g) (hh : g ≤ᵀᶠ h) : f ≤ᵀᶠ h := by
  generalize z : (↑f:ℕ→.ℕ)=x at hg
  simp only [TuringReducible,z] at *
  induction hg with
  | zero => exact Nat.RecursiveIn.zero
  | succ => exact Nat.RecursiveIn.succ
  | left => exact Nat.RecursiveIn.left
  | right => exact Nat.RecursiveIn.right
  | oracle => exact hh
  | pair hf hh hf_ih hh_ih => (expose_names; exact Nat.RecursiveIn.pair hf_ih hh_ih)
  | comp hf hh hf_ih hh_ih => (expose_names; exact Nat.RecursiveIn.comp hf_ih hh_ih)
  | prec hf hh hf_ih hh_ih => (expose_names; exact Nat.RecursiveIn.prec hf_ih hh_ih)
  | rfind hf ih => (expose_names; exact Nat.RecursiveIn.rfind ih)

instance : IsTrans (ℕ→ℕ) TuringReducible := ⟨@TuringReducible.trans⟩
instance : IsPreorder (ℕ→ℕ) TuringReducible where refl := .refl
theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent := (AntisymmRel.setoid _ _).iseqv
@[refl] protected theorem TuringEquivalent.refl (f : ℕ→ℕ) : f ≡ᵀᶠ f := Equivalence.refl equivalence f
@[symm] theorem TuringEquivalent.symm {f g : ℕ→ℕ} (h : f ≡ᵀᶠ g) : g ≡ᵀᶠ f := Equivalence.symm equivalence h
@[trans] theorem TuringEquivalent.trans (f g h : ℕ→ℕ) (h₁ : f ≡ᵀᶠ g) (h₂ : g ≡ᵀᶠ h) : f ≡ᵀᶠ h := Equivalence.trans equivalence h₁ h₂

/--
Instance declaring that `Nat.RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ→ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

abbrev FuncTuringDegree :=
  Antisymmetrization _ TuringReducible
private instance : Preorder (ℕ→ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans
  lt := TuringReducibleStrict

open scoped Computability
open Encodable

/-
Join of two partial functions on two primcodable types.
-/
-- def gjoin {α β α' β' : Type} [Primcodable α] [Primcodable β] [Primcodable α'] [Primcodable β']
-- (f : α →. β) (g : α' →. β') : α ⊕ α' →. β ⊕ β' :=
--   λ x =>
--     match x with
--     | Sum.inl a => (f a).map (λ b => Sum.inl b)
--     | Sum.inr b => (g b).map (λ a' => Sum.inr a')

-- def liftPrimcodable {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) : ℕ →. ℕ :=
--   fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

-- def turingJoin (f g : ℕ →. ℕ) : ℕ →. ℕ :=
--   liftPrimcodable (gjoin f g)

-- infix :50 " ⊕ " => turingJoin

-- open Sum

-- def projL : ℕ →. ℕ :=
-- λ n =>
--   match decode (α := ℕ ⊕ ℕ) n with
--   | some (Sum.inl x) => Part.some x
--   | _                => Part.none

-- def projR : ℕ →. ℕ :=
--   fun n =>
--     match decode (α := ℕ ⊕ ℕ) n with
--     | some (Sum.inr x) => Part.some x
--     | _                => Part.none

-- lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀᶠ (f ⊕ g) := by
--   sorry

-- lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀᶠ (f ⊕ g) := by
--   sorry

-- lemma join_le (f g h : ℕ →. ℕ) (hf : f ≤ᵀᶠ h) (hg : g ≤ᵀᶠ h) : (f ⊕ g) ≤ᵀᶠ h := by
--   induction hf
--   case zero =>
--     simp [turingJoin]
--     sorry
--   all_goals {sorry}

-- def TuringDegree.add (a b : TuringDegree) : TuringDegree :=
--   Quotient.liftOn₂ a b (fun f g => ⟦f ⊕ g⟧)
--     (by {
--       intro f₁ f₂ g₁ g₂ hf hg
--       apply Quot.sound
--       simp [AntisymmRel, TuringReducible]
--       constructor
--       cases' hf with hf₁ hf₂
--       cases' hg with hg₁ hg₂
--       all_goals {sorry}
--     })
