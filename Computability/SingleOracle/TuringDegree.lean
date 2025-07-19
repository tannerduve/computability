/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import Computability.SingleOracle.Oracle

/-!
# Turing Reducibility and Turing Degrees

This file defines Turing reducibility and Turing equivalence in terms of oracle computability,
as well as the notion of Turing degrees as equivalence classes under mutual reducibility.

## Main Definitions

* `TuringReducible f g`:
  The function `f` is Turing reducible to `g` if `f` is recursive in the singleton set `{g}`.
* `TuringEquivalent f g`:
  Functions `f` and `g` are Turing equivalent if they are mutually Turing reducible.
* `TuringDegree`:
  The type of Turing degrees, given by the quotient of `ℕ →. ℕ` under `TuringEquivalent`.

## Notation

* `f ≤ᵀ g`: `f` is Turing reducible to `g`.
* `f ≡ᵀ g`: `f` is Turing equivalent to `g`.

## Implementation Notes

We define `TuringDegree` as the `Antisymmetrization` of the preorder of partial functions under
Turing reducibility. This gives a concrete representation of degrees as equivalence classes.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers*, Vol. I.

## Tags

Computability, Turing Degrees, Reducibility, Equivalence Relation
-/


/--
`f` is Turing reducible to `g` if `f` is partial recursive given access to the oracle `g`
-/
abbrev TuringReducible (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn g f

abbrev TuringReducibleStrict (f g : ℕ →. ℕ) : Prop :=
  RecursiveIn g f ∧ ¬ RecursiveIn f g

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent
@[inherit_doc] scoped[Computability] infix:50 " <ᵀ " => TuringReducibleStrict

open scoped Computability

protected theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := by exact RecursiveIn.oracle
protected theorem TuringReducible.rfl : f ≤ᵀ f := .refl _

instance : IsRefl (ℕ →. ℕ) TuringReducible where refl _ := .rfl

theorem TuringReducible.trans (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) : f ≤ᵀ h := by
  induction hg
  · exact RecursiveIn.zero
  · exact RecursiveIn.succ
  · exact RecursiveIn.left
  · exact RecursiveIn.right
  · exact hh
  · (expose_names; exact RecursiveIn.pair hf_ih hh_ih)
  · (expose_names; exact RecursiveIn.comp hf_ih hh_ih)
  · (expose_names; exact RecursiveIn.prec hf_ih hh_ih)
  · (expose_names; exact RecursiveIn.rfind hf_ih)

instance : IsTrans (ℕ →. ℕ) TuringReducible :=
  ⟨@TuringReducible.trans⟩

instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := .refl

theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

@[refl]
protected theorem TuringEquivalent.refl (f : ℕ →. ℕ) : f ≡ᵀ f :=
  Equivalence.refl equivalence f

@[symm]
theorem TuringEquivalent.symm {f g : ℕ →. ℕ} (h : f ≡ᵀ g) : g ≡ᵀ f :=
  Equivalence.symm equivalence h

@[trans]
theorem TuringEquivalent.trans (f g h : ℕ →. ℕ) (h₁ : f ≡ᵀ g) (h₂ : g ≡ᵀ h) : f ≡ᵀ h :=
  Equivalence.trans equivalence h₁ h₂

/--
Instance declaring that `RecursiveIn` is a preorder.
-/
instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := TuringReducible.refl
  trans := @TuringReducible.trans

abbrev FuncTuringDegree :=
  Antisymmetrization _ TuringReducible
private instance : Preorder (ℕ →. ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans

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

-- lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀ (f ⊕ g) := by
--   sorry

-- lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀ (f ⊕ g) := by
--   sorry

-- lemma join_le (f g h : ℕ →. ℕ) (hf : f ≤ᵀ h) (hg : g ≤ᵀ h) : (f ⊕ g) ≤ᵀ h := by
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
