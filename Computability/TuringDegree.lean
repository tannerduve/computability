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
Join of two partial functions on two primcodable types.
-/
def gjoin {α β α' β' : Type} [Primcodable α] [Primcodable β] [Primcodable α'] [Primcodable β']
(f : α →. β) (g : α' →. β') : α ⊕ α' →. β ⊕ β' :=
  λ x =>
    match x with
    | Sum.inl a => (f a).map (λ b => Sum.inl b)
    | Sum.inr b => (g b).map (λ a' => Sum.inr a')

def liftPrimcodable {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) : ℕ →. ℕ :=
  fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

def turingJoin (f g : ℕ →. ℕ) : ℕ →. ℕ :=
  liftPrimcodable (gjoin f g)

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

-- Must prove other join lemmas to prove this, bottom are equivalent I believe
lemma get_from_join {f g : ℕ →. ℕ} : RecursiveIn (O ∪ {f ⊕ g}) f := sorry
lemma get_from_join' {f g : ℕ →. ℕ} (fgmem : (f ⊕ g) ∈ O) : RecursiveIn (O) f := sorry

lemma join_comm (f g : ℕ →. ℕ) : (f ⊕ g) = (g ⊕ f) :=
  sorry

lemma join_add_oracles_equiv_simple : ∀ f g h, RecursiveIn {f, g} h ↔ RecursiveIn {f ⊕ g} h := by
  sorry

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
    apply (join_add_oracles_equiv_simple f g (f ⊕ g)).mpr
    apply RecursiveIn.oracle
    rfl
  case pair _ _ _ recj reck => exact RecursiveIn.pair recj reck
  case comp _ _ _ _ recj reck => exact RecursiveIn.comp recj reck
  case prec _ _ _ _ recj reck => exact RecursiveIn.prec recj reck
  case rfind _ _ recj => exact RecursiveIn.rfind recj


#check finite_or_infinite
def join_collapse_finite (O: Set (ℕ →. ℕ)) : ℕ →. ℕ :=
  sorry

/--
To show that single oracle computation is equivalent (might need to assume O countable)
-/
lemma collapse_oracles {O f} : RecursiveIn O f -> ∃ o : ℕ →. ℕ, RecursiveIn {o} f := by
  sorry

#check RecursiveIn.of_eq

lemma join_inv_left_rec_from_join (f g : ℕ →. ℕ) :
  (λ n => Part.bind ((f ⊕ g) (encode (Sum.inl n : ℕ ⊕ ℕ))) projL) ≤ᵀ (f ⊕ g) := by
    simp
    unfold projL
    unfold turingJoin
    sorry

lemma decode_encode_helper : ∀ y: ℕ ⊕ ℕ, decodeSum (encodeSum y) = some y := by
  intro y
  simp [decodeSum, encodeSum]
  induction y <;> simp

lemma helper {n} : (Denumerable.ofNat (ℕ ⊕ ℕ) (2 * n)) = Sum.inl n := by
  induction n
  case zero =>
    unfold Denumerable.ofNat
    -- rw [Denumerable.decode_eq_ofNat (α := ℕ) (n := 2 * 0)]
    sorry
  case succ k ih =>
    unfold Denumerable.ofNat at *
    rw [mul_add]
    unfold decode at *
    simp
    sorry

lemma extract_left_from_join (f g : ℕ →. ℕ) :
    f = λ n => Part.bind ((f ⊕ g) (encode (Sum.inl n : ℕ ⊕ ℕ))) projL := by
  funext n
  simp [turingJoin, liftPrimcodable, gjoin]
  unfold projL
  simp [decode, encode, decode_encode_helper]
  sorry

lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀ (f ⊕ g) := by
  unfold TuringReducible
  unfold turingJoin
  unfold gjoin
  sorry

lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀ (f ⊕ g) := by
  sorry

lemma join_le (f g h : ℕ →. ℕ) (hf : f ≤ᵀ h) (hg : g ≤ᵀ h) : (f ⊕ g) ≤ᵀ h := by
  induction hf
  case zero =>
    simp [turingJoin]
    sorry
  all_goals {sorry}

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

-- def TuringDegree.le : (a b : TuringDegree) -> Prop :=
--   fun a b => Quotient.

-- Can't even define
-- lemma TuringDegree.add_le {a b : TuringDegree} : a ≤ᵀ a.add(b) := sorry

#check TuringReducible.trans

lemma use_function_from_oracle
  (f : ℕ → ℕ) (g : ℕ → ℕ →. ℕ) (hf : RecursiveIn O f) (hg : RecursiveIn₂ O g)
  : RecursiveIn O (λ n => g n (f n)) := by
  sorry
