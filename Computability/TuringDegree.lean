/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import Computability.Oracle

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
  RecursiveIn {g} f

/--
`f` is Turing equivalent to `g` if `f` is reducible to `g` and `g` is reducible to `f`.
-/
abbrev TuringEquivalent (f g : ℕ →. ℕ) : Prop :=
  AntisymmRel TuringReducible f g

@[inherit_doc] scoped[Computability] infix:50 " ≤ᵀ " => TuringReducible
@[inherit_doc] scoped[Computability] infix:50 " ≡ᵀ " => TuringEquivalent

open scoped Computability

protected theorem TuringReducible.refl (f : ℕ →. ℕ) : f ≤ᵀ f := .oracle _ <| by simp
protected theorem TuringReducible.rfl : f ≤ᵀ f := .refl _

instance : IsRefl (ℕ →. ℕ) TuringReducible where refl _ := .rfl

theorem TuringReducible.trans (hg : f ≤ᵀ g) (hh : g ≤ᵀ h) : f ≤ᵀ h := by
  induction' hg with g' hg g' h' _ _ ih₁ ih₂ g' h' _ _ ih₁ ih₂ g' h' _ _ ih₁ ih₂ g' _ ih
  repeat {constructor}
  · rw [Set.mem_singleton_iff] at hg; rw [hg]; exact hh
  · case pair =>
    apply RecursiveIn.pair ih₁ ih₂
  · case comp =>
    apply RecursiveIn.comp ih₁ ih₂
  · case prec =>
    apply RecursiveIn.prec ih₁ ih₂
  · case rfind =>
    apply RecursiveIn.rfind ih

instance : IsTrans (ℕ →. ℕ) TuringReducible :=
  ⟨@TuringReducible.trans⟩

instance : IsPreorder (ℕ →. ℕ) TuringReducible where
  refl := .refl

theorem TuringEquivalent.equivalence : Equivalence TuringEquivalent :=
  (AntisymmRel.setoid _ _).iseqv

#check Quotient
#check Setoid

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

/--
Turing degrees are the equivalence classes of partial functions under Turing equivalence.
-/
abbrev TuringDegree :=
  Antisymmetrization _ TuringReducible

private instance : Preorder (ℕ →. ℕ) where
  le := TuringReducible
  le_refl := .refl
  le_trans _ _ _ := TuringReducible.trans

instance TuringDegree.instPartialOrder : PartialOrder TuringDegree :=
  instPartialOrderAntisymmetrization

open scoped Computability
open Encodable

/-
Using Computation from the Oracles
-/

lemma use_oracle_computation_from_pair {O : Set (ℕ →. ℕ)} (f g h : ℕ →. ℕ)
  (recf : RecursiveIn O f) (recg : RecursiveIn O g) (fgh : RecursiveIn {f, g} h) :
  RecursiveIn O h := by
  induction fgh
  repeat {constructor}
  case oracle _ k =>
    cases' k with H H
    rw [H]
    assumption
    cases' H with H1 H1
    assumption
  case pair recj reck => exact RecursiveIn.pair recj reck
  case comp recj reck => exact RecursiveIn.comp recj reck
  case prec recj reck => exact RecursiveIn.prec recj reck
  case rfind recj => exact RecursiveIn.rfind recj

lemma use_function_from_oracle
  (f : ℕ → ℕ) (g : ℕ → ℕ →. ℕ) (hf : RecursiveIn O f) (hg : RecursiveIn₂ O g)
  : RecursiveIn O (λ n => g n (f n)) := by
  sorry

/-
Join Definition
-/

def gjoin {α β α' β' : Type} [Primcodable α] [Primcodable β] [Primcodable α'] [Primcodable β']
(f : α →. β) (g : α' →. β') : α ⊕ α' →. β ⊕ β' :=
  λ x =>
    match x with
    | Sum.inl a => (f a).map (λ b => Sum.inl b)
    | Sum.inr b => (g b).map (λ a' => Sum.inr a')

def turingJoin (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  liftPrim (gjoin f g)

def turing_join_interweave (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  fun n =>
    if n % 2 == 0 then f (n / 2) else g (n / 2)

infix :50 " ⊕ " => turingJoin

open Sum

def projL : ℕ →. ℕ :=
λ n =>
  match decode (α := ℕ ⊕ ℕ) n with
  | some (Sum.inl x) => Part.some x
  | _                => Part.none

def projR : ℕ →. ℕ :=
  fun n =>
    match decode (α := ℕ ⊕ ℕ) n with
    | some (Sum.inr x) => Part.some x
    | _                => Part.none


def encode_decoded (f g : ℕ →. ℕ) := fun n ↦
    Part.map encode
      (match Denumerable.ofNat (ℕ ⊕ ℕ) n with
      | inl a => Part.map (fun b ↦ inl b) (f a)
      | inr b => Part.map (fun a' ↦ inr a') (g b))

/-
Join Lemmas
-/

lemma join_comm (f g : ℕ →. ℕ) : (f ⊕ g) = (g ⊕ f) :=
  sorry

lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀ (f ⊕ g) := by
  unfold turingJoin TuringReducible gjoin liftPrim
  simp
  sorry

lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀ (f ⊕ g) := by sorry

lemma join_le (f g h : ℕ →. ℕ) (hf : f ≤ᵀ h) (hg : g ≤ᵀ h) : (f ⊕ g) ≤ᵀ h := by
  induction hf
  case zero =>
    simp [turingJoin]
    sorry
  all_goals {sorry}

lemma join_rec_in_funcs : RecursiveIn {f, g} (f ⊕ g) := sorry

lemma get_from_join {f g : ℕ →. ℕ} : RecursiveIn (O ∪ {f ⊕ g}) f := by sorry
/-
Join used in Oracles
-/

lemma join_add_oracles_equiv_simple {f g h : ℕ →. ℕ} : RecursiveIn {f, g} h ↔ RecursiveIn {f ⊕ g} h := by
  constructor
  case mp =>
    intro H
    induction H; repeat {constructor}
    case oracle func funcmem =>
      cases' funcmem
      case inl funcf =>
        rw [funcf]
        exact left_le_join f g
      case inr funcg =>
        cases' funcg
        exact right_le_join f g
    case pair j k _ _ recj reck =>
      apply RecursiveIn.pair recj reck
    case comp j k _ _ recj reck =>
      apply RecursiveIn.comp recj reck
    case prec j k _ _ recj reck =>
      apply RecursiveIn.prec recj reck
    case rfind j _ recj => apply RecursiveIn.rfind recj
  case mpr =>
    intro H
    induction H; repeat {constructor}
    case oracle func funcmem =>
      cases' funcmem
      exact join_rec_in_funcs
    case pair j k _ _ recj reck =>
      apply RecursiveIn.pair recj reck
    case comp j k _ _ recj reck =>
      apply RecursiveIn.comp recj reck
    case prec j k _ _ recj reck =>
      apply RecursiveIn.prec recj reck
    case rfind j _ recj => apply RecursiveIn.rfind recj

lemma join_add_oracles_equiv : RecursiveIn (O ∪ {f, g}) h ↔ RecursiveIn (O ∪ {f ⊕ g}) h := by
  constructor
  intro H
  induction H
  repeat {constructor}
  case oracle j jmem =>
    cases' jmem with H H
    constructor
    left
    assumption
    cases' H with jf jg
    rw [jf]
    exact get_from_join
    cases' jg
    rw [join_comm]
    exact get_from_join
  case pair j k _ _ recj reck =>
    apply RecursiveIn.pair recj reck
  case comp j k _ _ recj reck =>
    apply RecursiveIn.comp recj reck
  case prec j k _ _ recj reck =>
    apply RecursiveIn.prec recj reck
  case rfind j _ recj => apply RecursiveIn.rfind recj

  intro H
  induction H
  repeat {constructor}
  case oracle j jmem =>
    cases' jmem with H H
    constructor
    left
    assumption
    cases' H with jf jg
    apply use_oracle_computation_from_pair
    apply RecursiveIn.oracle f
    right
    left
    rfl
    apply RecursiveIn.oracle g
    right
    right
    rfl
    exact join_rec_in_funcs
  case pair _ _ _ recj reck => exact RecursiveIn.pair recj reck
  case comp _ _ _ _ recj reck => exact RecursiveIn.comp recj reck
  case prec _ _ _ _ recj reck => exact RecursiveIn.prec recj reck
  case rfind _ _ recj => exact RecursiveIn.rfind recj


/-
Degree Operations
1. Jump
2. Add
3. Join
4. Meet
-/

-- lemma jump_lifts : ∀ (f g : ℕ →. ℕ), f ≡ᵀ g → turing_degree_mk (f⌜) = turing_degree_mk (g⌜) := by
--   intros f g H
--   unfold turing_degree_mk
--   cases' H with fg gf
--   have fg_jump : f⌜ ≤ᵀ g⌜ := (jump_monotone f g).mp fg
--   have gf_jump : g⌜ ≤ᵀ f⌜ := (jump_monotone g f).mp gf
--   have equiv : f⌜ ≡ᵀ g⌜ := ⟨fg_jump, gf_jump⟩
--   apply Quotient.sound equiv

-- def TuringDegree.jump : TuringDegree → TuringDegree :=
--   Quotient.lift (fun f => ⟦f⌜⟧) jump_lifts

-- notation:100 f"⌜" => jump f

infix :50 " ⊕ " => TuringDegree.add

def TuringDegree.add (a b : TuringDegree) : TuringDegree :=
  Quotient.liftOn₂ a b (fun f g => ⟦f ⊕ g⟧)
    (by {
      intro f₁ f₂ g₁ g₂ hf hg
      apply Quot.sound
      simp [AntisymmRel]
      constructor
      cases' hf with hf₁ hf₂
      cases' hg with hg₁ hg₂
      case a.left =>
        have f₁g₁g₂ : f₁ ≤ᵀ (g₁ ⊕ g₂) := TuringReducible.trans hf₁ (left_le_join g₁ g₂)
        have f₂g₁g₂ : f₂ ≤ᵀ (g₁ ⊕ g₂) := TuringReducible.trans hg₁ (right_le_join g₁ g₂)
        apply join_le f₁ f₂ (g₁ ⊕ g₂) f₁g₁g₂ f₂g₁g₂
      case a.right =>
        cases' hf with hf₁ hf₂
        cases' hg with hg₁ hg₂
        have gf₁f₂ : g₁ ≤ᵀ (f₁ ⊕ f₂) := TuringReducible.trans hf₂ (left_le_join f₁ f₂)
        have g₂f₁f₂ : g₂ ≤ᵀ (f₁ ⊕ f₂) := TuringReducible.trans hg₂ (right_le_join f₁ f₂)
        apply join_le g₁ g₂ (f₁ ⊕ f₂) gf₁f₂ g₂f₁f₂
    })


infix :50 " ⊕ " => TuringDegree.add
