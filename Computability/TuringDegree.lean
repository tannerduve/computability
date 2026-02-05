/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import Computability.Oracle
import Mathlib.Tactic.Cases
import Mathlib.Tactic.NormNum
import Aesop
import Mathlib.Computability.Halting

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

/-
`projL n` is `Part.some (n / 2)` if `n` is even, and `Part.none` if `n` is odd.
-/
lemma projL_eq_explicit (n : ℕ) : projL n = if n % 2 = 0 then Part.some (n / 2) else Part.none := by
  have h_projL : ∀ n : ℕ, projL n = if n % 2 = 0 then Part.some (n / 2) else Part.none := by
    intro n
    have h_decode : decode (α := ℕ ⊕ ℕ) n = if n % 2 = 0 then some (Sum.inl (n / 2)) else some (Sum.inr ((n - 1) / 2)) := by
      by_cases h_even : n % 2 = 0;
      · cases n <;> simp_all only [Nat.zero_mod, Denumerable.decode_eq_ofNat, ↓reduceIte, Nat.zero_div, Option.some.injEq]
        rfl;
        rename_i n₁
        rw [ Denumerable.ofNat ];
        simp [ Encodable.decode ];
        simp [ Encodable.decodeSum];
        cases Nat.even_or_odd' n₁ ;
        rename_i h
        cases h with
        | inl h_1 =>
          subst h_1
          simp_all only [Nat.mul_add_mod_self_left, Nat.mod_succ, one_ne_zero]
        | inr h_2 =>
          subst h_2
          simp_all only [Nat.bodd_succ, Nat.bodd_mul, Nat.bodd_zero, Bool.not_false, Bool.not_true, Bool.false_and,
            Nat.div2_succ, Nat.div2_bit0, Nat.succ_eq_add_one, cond_false, cond_true, Option.get_some, inl.injEq]
          omega;
      · obtain ⟨ k, rfl ⟩ := Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp h_even ) ; simp [ Encodable.decode ] ;
        simp [ Encodable.decodeSum ];
        cases k <;> rfl
    unfold projL; aesop;
  exact h_projL n

/-
`projL` and `projR` are partial recursive.
-/
lemma projL_partrec : Partrec projL := by
  have h_projL_bind : ∃ (f : ℕ ⊕ ℕ →. ℕ), Partrec f ∧ projL = liftPrimcodable f := by
    use fun x => Part.bind ( Part.some x ) fun a => match a with | Sum.inl x => Part.some x | Sum.inr _ => Part.none;
    constructor;
    · convert Partrec.sumCasesOn_right _ _;
      rotate_left;
      exact ℕ ⊕ ℕ;
      exact ℕ;
      exact ℕ;
      exact ℕ;
      all_goals try infer_instance;
      exact fun x => x;
      exact fun x y => y;
      exact fun x y => Part.none;
      · exact Computable.id;
      · exact Computable.snd;
      · simp_all only [Part.bind_some]
        apply Iff.intro
        · intro a hh
          convert a using 1;
          exact funext fun x => by cases x <;> rfl;
        · intro a
          convert a _;
          · cases ‹_› <;> rfl;
          · exact Partrec.none;
    · funext n
      simp [projL, liftPrimcodable];
      cases Denumerable.ofNat ( ℕ ⊕ ℕ ) n <;> simp [ * ];
  obtain ⟨w, h⟩ := h_projL_bind
  obtain ⟨lt, right⟩ := h
  simp_all only
  exact Partrec.nat_iff.mpr lt

lemma projR_partrec : Partrec projR := by
  have h_projR : projR = fun n => match decode (α := ℕ ⊕ ℕ) n with | some (Sum.inr x) => Part.some x | _ => Part.none := by
    funext n; exact rfl;
  set f : ℕ ⊕ ℕ →. ℕ := fun x => match x with | Sum.inr x => Part.some x | _ => Part.none;
  have h_f : Partrec f := by
    have h_f : Partrec (fun x : ℕ ⊕ ℕ => match x with | Sum.inr x => Part.some x | _ => Part.none) := by
      have : Partrec (fun x : ℕ ⊕ ℕ => match x with | Sum.inr x => Part.some x | _ => Part.none) := by
        have : Partrec (fun x : ℕ ⊕ ℕ => match x with | Sum.inl x => Part.none | Sum.inr x => Part.some x) := by
          have h_f : Partrec (fun x : ℕ ⊕ ℕ => match x with | Sum.inl x => Part.none | Sum.inr x => Part.some x) := by
            have : Partrec (fun x : ℕ ⊕ ℕ => Sum.elim (fun _ => Part.none) (fun x => Part.some x) x) := by
              apply_rules [ Partrec.sumCasesOn_left, Partrec.comp ];
              any_goals exact Computable.id;
              · exact Partrec.none;
              · exact Computable.snd
            grind;
          exact h_f
        grind
      exact this;
    exact h_f;
  have h_projR : projR = fun n => Part.bind (decode (α := ℕ ⊕ ℕ) n) f := by
    aesop;
  rw [h_projR];
  exact Partrec.nat_iff.mpr h_f

lemma left_le_join (f g : ℕ →. ℕ) : f ≤ᵀ (f ⊕ g) := by
  have h_f : ∀ n, f n = (turingJoin f g (2 * n)).bind projL := by
    unfold turingJoin; intro n;
    unfold liftPrimcodable gjoin;
    simp_all only [Denumerable.decode_eq_ofNat, Part.coe_some, Part.bind_some, Part.bind_map]
    split
    next x a heq =>
      simp_all only [Part.bind_map, encode_inl, encode_nat]
      cases x with
      | inl val =>
         rw [ show a = n from ?_ ];
          ·
          have h_projL : ∀ y : ℕ, projL (2 * y) = Part.some y := by
            intro y; rw [ projL_eq_explicit ] ; norm_num;
          aesop;
         rw [ Denumerable.ofNat ] at heq;
         simp_all [ Encodable.decode ];
         simp_all [ Encodable.decodeSum ];
      | inr val_1 =>
        rw [ show a = n from ?_ ];
        · have h_projL : ∀ y : ℕ, projL (2 * y) = Part.some y := by
            intro y; rw [ projL_eq_explicit ] ; norm_num;
          aesop;
        · rw [ Denumerable.ofNat ] at heq;
          simp_all [ Encodable.decode ];
          simp_all [ Encodable.decodeSum ];
    next x b heq =>
      simp_all only [Part.bind_map, encode_inr, encode_nat]
      cases x with
      | inl val =>
      have h_projL : ∀ y, projL (2 * y) = Part.some y := by
        intro y; rw [ projL_eq_explicit ] ; norm_num [ Nat.mul_mod ] ;
      have := h_projL n; unfold projL at this; aesop;
      | inr val_1 =>
      have h_projL : ∀ y, projL (2 * y) = Part.some y := by
        intro y; rw [ projL_eq_explicit ] ; norm_num [ Nat.mul_mod ] ;
      have := h_projL n; unfold projL at this; aesop;
  have h_projL : RecursiveIn {turingJoin f g} projL := by
    apply Nat.Partrec.recursiveIn;
    convert projL_partrec;
    ext;
    exact Iff.symm Partrec.nat_iff;
  have h_encodeInl : RecursiveIn {turingJoin f g} (fun n => Part.some (2 * n)) := by
    have h_double : RecursiveIn {turingJoin f g} (fun n => Part.some (2 * n)) := by
      have h_double_primrec : Computable (fun n : ℕ => 2 * n) := by
        have h_double_primrec : Primrec (fun n : ℕ => 2 * n) := by
          exact Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.id );
        exact Primrec.to_comp h_double_primrec
      apply Nat.Partrec.recursiveIn;
      exact Partrec.nat_iff.mp h_double_primrec;
    exact h_double;
  have h_f_rec : RecursiveIn {turingJoin f g} f := by
    convert RecursiveIn.comp _ _;
    rotate_left;
    exact fun n => projL n;
    exact fun n => turingJoin f g ( 2 * n );
    · exact h_projL;
    · convert RecursiveIn.comp _ _;
      rotate_left;
      exact fun n => turingJoin f g n;
      exact fun n => Part.some ( 2 * n );
      · exact RecursiveIn.oracle _ ( Set.mem_singleton _ );
      · assumption;
      · norm_num at *;
    · exact h_f _;
  exact h_f_rec

open Primrec Nat.Partrec Part

lemma projR_eq (n : ℕ) : projR n = if n.bodd then Part.some n.div2 else Part.none := by
  unfold projR;
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp [ Encodable.decode ] <;> simp [Encodable.decodeSum];

open Primrec Nat.Partrec Part

def check_projR (p : ℕ) : ℕ :=
  let (n, k) := Nat.unpair p
  if k = n.div2 ∧ n.bodd then 0 else 1

lemma check_projR_primrec : Primrec check_projR := by
  have h_cond : Primrec (fun p : ℕ × ℕ => if p.2 = p.1.div2 then 0 else 1) ∧ Primrec (fun p : ℕ × ℕ => if p.1.bodd = Bool.true then 0 else 1) := by
    constructor;
    · have h_cond : Primrec (fun p : ℕ × ℕ => if p.2 = p.1.div2 then 0 else 1) := by
        have h_div2 : Primrec (fun p : ℕ => p.div2) := by
          have h_div : Primrec (fun p : ℕ × ℕ => p.1 / p.2) := by
            exact Primrec.nat_div.comp (Primrec.fst) (Primrec.snd);
          convert h_div.comp ( show Primrec fun p : ℕ => ( p, 2 ) from ?_ ) using 1;
          · norm_num [ Nat.div2_val ];
          · exact Primrec.pair Primrec.id ( Primrec.const 2 )
        have h_cond : Primrec (fun p : ℕ × ℕ => if p.2 = p.1.div2 then true else false) := by
          convert Primrec.eq.comp ( Primrec.snd ) ( h_div2.comp ( Primrec.fst ) ) using 1;
          exact Iff.symm primrecPred_iff_primrec_decide;
        have h_cond : Primrec (fun p : ℕ × ℕ => if p.2 = p.1.div2 then 0 else 1) := by
          have h_if : Primrec (fun b : Bool => if b then 0 else 1) := by
            exact dom_bool fun b ↦ if b = true then 0 else 1
          simpa using h_if.comp h_cond;
        exact h_cond;
      assumption;
    · have h_odd : Primrec (fun n : ℕ => if n.bodd then 0 else 1) := by
        have h_odd : Primrec (fun n : ℕ => n.bodd) := by
          convert Primrec.nat_bodd using 1;
        have h_bool_to_nat : Primrec (fun b : Bool => if b then 0 else 1) := by
          exact dom_bool fun b ↦ if b = true then 0 else 1;
        exact h_bool_to_nat.comp h_odd;
      exact h_odd.comp ( Primrec.fst );
  have h_cond : Primrec (fun p : ℕ × ℕ => if p.2 = p.1.div2 ∧ p.1.bodd = Bool.true then 0 else 1) := by
    have h_and : Primrec (fun p : ℕ × ℕ => if p.2 = p.1.div2 then 0 else 1) ∧ Primrec (fun p : ℕ × ℕ => if p.1.bodd = Bool.true then 0 else 1) := h_cond
    have h_and : Primrec (fun p : ℕ × ℕ => if p.2 = p.1.div2 ∧ p.1.bodd = Bool.true then 0 else 1) := by
      have h_and : Primrec (fun p : ℕ × ℕ => (if p.2 = p.1.div2 then 0 else 1) + (if p.1.bodd = Bool.true then 0 else 1)) := by
        apply Primrec.nat_add.comp (h_and.left) (h_and.right)
      have h_and : Primrec (fun p : ℕ × ℕ => if (if p.2 = p.1.div2 then 0 else 1) + (if p.1.bodd = Bool.true then 0 else 1) = 0 then 0 else 1) := by
        have h_and : Primrec (fun n : ℕ => if n = 0 then 0 else 1) := by
          convert Primrec.of_eq _ _;
          exact fun n => Nat.recOn n 0 fun _ _ => 1;
          · exact Primrec.nat_casesOn ( Primrec.id ) ( Primrec.const 0 ) ( Primrec.const 1 );
          · rintro ( _ | _ | n ) <;> rfl;
        convert h_and.comp ‹Primrec fun p : ℕ × ℕ => ( if p.2 = p.1.div2 then 0 else 1 ) + if p.1.bodd = Bool.true then 0 else 1› using 1;
      convert h_and using 2 ; aesop;
    exact h_and;
  exact h_cond

open Primrec Nat.Partrec Part Nat

lemma projR_eq_rfind (a : ℕ) : projR a = Nat.rfind fun n => (fun m => decide (m = 0)) <$> Part.some (check_projR (Nat.pair a n)) := by
  have h_projR_eq : projR a = if a.bodd then Part.some a.div2 else Part.none := by
    exact projR_eq a;
  unfold check_projR; aesop;

open Primrec Nat.Partrec Part Nat

lemma projR_partrec' : Nat.Partrec projR := by
  simpa using Partrec.nat_iff.mp projR_partrec

open Primrec Nat.Partrec Part Nat

def injR (n : ℕ) : ℕ := Encodable.encode (Sum.inr n : ℕ ⊕ ℕ)

lemma injR_primrec : Primrec injR := by
  have h_injR : Primrec (Sum.inr : ℕ → ℕ ⊕ ℕ) := by
    apply Primrec.sumInr;
  exact h_injR

lemma injR_partrec : Nat.Partrec (fun n => Part.some (injR n)) := by
  have h_id : Nat.Partrec (fun n : ℕ => Part.some n) := by
    apply Nat.Partrec.of_primrec; exact (by
    apply Nat.Primrec.id);
  convert h_id.comp _;
  simp [injR];
  rfl;
  have h_injR : Nat.Partrec (fun n => Part.some (2 * n + 1)) := by
    have h_primrec : Primrec (fun n => 2 * n + 1) := by
      exact Primrec.nat_add.comp ( Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.id ) ) ( Primrec.const 1 )
    convert Nat.Partrec.of_primrec ( show Nat.Primrec ( fun n => 2 * n + 1 ) from ?_ ) using 1;
    have h_pred : Nat.Primrec (fun n => n - 1) := by
      exact Nat.Primrec.pred;
    convert h_pred.comp h_primrec using 1;
  exact h_injR

lemma projR_injR (n : ℕ) : projR (injR n) = Part.some n := by
  simp [projR, injR];
  rw [ Denumerable.ofNat ];
  simp [ Encodable.decode ];
  simp [ Encodable.decodeSum ]

lemma turingJoin_injR (f g : ℕ →. ℕ) (n : ℕ) : turingJoin f g (injR n) = (g n).map injR := by
  simp [turingJoin];
  simp [liftPrimcodable];
  have h_den : Denumerable.ofNat (ℕ ⊕ ℕ) (injR n) = Sum.inr (Denumerable.ofNat ℕ n) := by
    conv => rw [ Denumerable.ofNat ] ;
    simp [ Encodable.decode ];
    simp [ Encodable.decodeSum ];
    simp [ injR ];
  aesop

lemma right_le_join (f g : ℕ →. ℕ) : g ≤ᵀ (f ⊕ g) := by
  have h_turing_join : forall n : ℕ, g n = (turingJoin f g (injR n)).bind projR := by
    intro n
    have h_turing_join : turingJoin f g (injR n) = (g n).map injR := by
      exact turingJoin_injR f g n;
    have h_bind : ∀ x : ℕ, projR (injR x) = Part.some x := by
      exact fun x ↦ projR_injR x;
    cases h : g n ; aesop;
  have h_rec_in : RecursiveIn {turingJoin f g} (fun n => (turingJoin f g (injR n)).bind projR) := by
    have h_injR : RecursiveIn {turingJoin f g} (fun n => Part.some (injR n)) := by
      have h_injR_primrec : Nat.Partrec (fun n => Part.some (injR n)) := by
        exact injR_partrec;
      convert Nat.Partrec.recursiveIn h_injR_primrec
    have h_projR : RecursiveIn {turingJoin f g} projR := by
      apply Nat.Partrec.recursiveIn; exact projR_partrec';
    have h_turingJoin : RecursiveIn {turingJoin f g} (fun n => turingJoin f g n) := by
      apply_rules [ RecursiveIn.oracle ];
    have h_comp : RecursiveIn {turingJoin f g} (fun n => (turingJoin f g n).bind projR) := by
      exact RecursiveIn.comp h_projR h_turingJoin;
    convert h_comp.comp h_injR using 1;
    exact funext fun n => by simp +decide ;
  simpa only [ ← h_turing_join ] using h_rec_in

theorem RecursiveIn_cond_const {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f : ℕ →. ℕ} (hc : Computable c) (hf : RecursiveIn O f) (k : ℕ) :
    RecursiveIn O (fun n => bif (c n) then f n else (Part.some k)) := by
  classical
  -- Monotonicity of `RecursiveIn` in the oracle set
  have recursiveIn_mono {O₁ O₂ : Set (ℕ →. ℕ)} (hsub : O₁ ⊆ O₂) {g : ℕ →. ℕ} :
      RecursiveIn O₁ g → RecursiveIn O₂ g := by
    intro hg
    induction hg with
    | zero => exact RecursiveIn.zero
    | succ => exact RecursiveIn.succ
    | left => exact RecursiveIn.left
    | right => exact RecursiveIn.right
    | oracle g hg => exact RecursiveIn.oracle g (hsub hg)
    | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
    | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
    | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
    | rfind _ ih => exact RecursiveIn.rfind ih

  -- Any partial recursive function is recursive relative to any oracle set
  have partrec_to_recursiveIn {g : ℕ →. ℕ} (hg : Nat.Partrec g) : RecursiveIn O g := by
    have hg0 : RecursiveIn ({} : Set (ℕ →. ℕ)) g := (recursiveIn_empty_iff_partrec).2 hg
    exact
      recursiveIn_mono (O₁ := ({} : Set (ℕ →. ℕ))) (O₂ := O) (by
        intro x hx
        cases hx) hg0

  -- identity function
  have hid : RecursiveIn O (fun n : ℕ => n) := by
    apply partrec_to_recursiveIn
    exact (Partrec.nat_iff).1 (Computable.id.partrec)

  -- boolean code `encode (c n)`
  have hcode : RecursiveIn O (fun n : ℕ => encode (c n)) := by
    apply partrec_to_recursiveIn
    have hcomp : Computable (fun n : ℕ => encode (c n)) := (Computable.encode.comp hc)
    exact (Partrec.nat_iff).1 hcomp.partrec

  -- pairing `n ↦ Nat.pair n (encode (c n))`
  let pairFn : ℕ →. ℕ := fun n => Nat.pair <$> (show Part ℕ from n) <*> (show Part ℕ from encode (c n))
  have hpair : RecursiveIn O pairFn := by
    simpa [pairFn] using (RecursiveIn.pair hid hcode)

  -- base function for recursion: constant `k`
  let base : ℕ →. ℕ := fun _ : ℕ => (k : ℕ)
  have hbase : RecursiveIn O base := by
    apply partrec_to_recursiveIn
    simpa [base] using (Partrec.nat_iff).1 ((Computable.const k).partrec)

  -- step function: ignore IH, return `f a`
  let step : ℕ →. ℕ := fun p : ℕ => (Nat.unpair p).1 >>= f
  have hstep : RecursiveIn O step := by
    simpa [step] using (RecursiveIn.comp hf RecursiveIn.left)

  -- primitive recursion on the encoded boolean
  let precFn : ℕ →. ℕ :=
    fun p : ℕ =>
      let (a, n) := Nat.unpair p
      n.rec (base a) (fun y IH => do
        let i ← IH
        step (Nat.pair a (Nat.pair y i)))

  have hprec : RecursiveIn O precFn := by
    simpa [precFn] using (RecursiveIn.prec hbase hstep)

  -- compose primitive recursion with pairing
  let mainFn : ℕ →. ℕ := fun n => pairFn n >>= precFn
  have hmain : RecursiveIn O mainFn := by
    simpa [mainFn] using (RecursiveIn.comp hprec hpair)

  -- show `mainFn` agrees with the desired conditional
  have hEq : mainFn = (fun n => bif (c n) then f n else Part.some k) := by
    funext n
    cases h : c n <;>
      simp [mainFn, pairFn, precFn, base, step, h, Seq.seq, Nat.unpair_pair]

  simpa [hEq] using hmain


def eq01 : ℕ →. ℕ := fun p => Part.some (if (Nat.unpair p).1 = (Nat.unpair p).2 then 0 else 1)

theorem eq01_natPartrec: Nat.Partrec eq01 := by
  have hcomp : Computable (fun p : ℕ => if (Nat.unpair p).1 = (Nat.unpair p).2 then (0 : ℕ) else 1) := by
    -- A computable decider for equality on pairs of naturals
    have hEq : Computable (fun q : ℕ × ℕ => decide (q.1 = q.2)) := by
      have hprim : Primrec (fun q : ℕ × ℕ => decide (q.1 = q.2)) := by
        simpa using
          (PrimrecPred.decide (p := fun q : ℕ × ℕ => q.1 = q.2)
            (Primrec.eq : PrimrecPred fun q : ℕ × ℕ => q.1 = q.2))
      exact Primrec.to_comp hprim
    have hdec : Computable (fun p : ℕ => decide ((Nat.unpair p).1 = (Nat.unpair p).2)) :=
      Computable.comp hEq Computable.unpair
    have hcond : Computable (fun p : ℕ => cond (decide ((Nat.unpair p).1 = (Nat.unpair p).2)) (0 : ℕ) 1) := by
      have h0 : Computable (fun _ : ℕ => (0 : ℕ)) := Computable.const 0
      have h1 : Computable (fun _ : ℕ => (1 : ℕ)) := Computable.const 1
      simpa using
        (Computable.cond (c := fun p : ℕ => decide ((Nat.unpair p).1 = (Nat.unpair p).2))
          (f := fun _ : ℕ => (0 : ℕ)) (g := fun _ : ℕ => (1 : ℕ)) hdec h0 h1)
    refine Computable.of_eq hcond ?_
    intro p
    by_cases h : (Nat.unpair p).1 = (Nat.unpair p).2 <;> simp [h]
  have hpart : _root_.Partrec eq01 := by
    -- `Computable.partrec` gives partial recursiveness for the coerced total function;
    -- this agrees pointwise with `eq01`.
    refine _root_.Partrec.of_eq (Computable.partrec hcomp) ?_
    intro p
    by_cases h : (Nat.unpair p).1 = (Nat.unpair p).2 <;> simp [eq01, h]
  exact (Partrec.nat_iff).1 hpart

theorem eq01_recursiveIn (O : Set (ℕ →. ℕ)) : RecursiveIn O eq01 := by
  have hpart : Nat.Partrec eq01 := eq01_natPartrec
  exact Nat.Partrec.recursiveIn (O := O) hpart


theorem eq01_rfind_none: Nat.rfind (fun k => (fun m : ℕ => m = 0) <$>
    ((Nat.pair <$> (Part.none : Part ℕ) <*> Part.some k) >>= eq01)) = (Part.none : Part ℕ) := by
  classical
  refine Nat.rfind_zero_none
    (p := fun k => (fun m : ℕ => m = 0) <$>
      ((Nat.pair <$> (Part.none : Part ℕ) <*> Part.some k) >>= eq01)) ?_
  simp [Seq.seq]

theorem eq01_rfind_some (n : ℕ) :
  Nat.rfind (fun k => (fun m : ℕ => m = 0) <$>
    ((Nat.pair <$> (Part.some n : Part ℕ) <*> Part.some k) >>= eq01)) = Part.some n := by
  classical
  -- define the predicate used by `Nat.rfind`
  let p : ℕ →. Bool := fun k =>
    (fun m : ℕ => m = 0) <$>
      ((Nat.pair <$> (Part.some n : Part ℕ) <*> Part.some k) >>= eq01)
  -- it suffices to show that `n` is the (unique) element of `Nat.rfind p`
  refine Part.mem_right_unique ?_ (Part.mem_some n)
  -- characterize membership in `Nat.rfind`
  refine (Nat.mem_rfind).2 ?_
  constructor
  · -- `p n` evaluates to `true`
    simp [eq01, Nat.unpair_pair, Seq.seq]
  · intro m hm
    have hne : n ≠ m := Nat.ne_of_gt hm
    -- for `m < n`, `p m` evaluates to `false`
    simp [eq01, Nat.unpair_pair, Seq.seq, hne]

theorem eq01_rfind (v : Part ℕ) :
  Nat.rfind (fun k => (fun m : ℕ => m = 0) <$> ((Nat.pair <$> v <*> Part.some k) >>= eq01)) = v := by
  classical
  refine Part.induction_on v ?_ ?_
  · simpa using eq01_rfind_none
  · intro n
    simpa using eq01_rfind_some (n := n)


theorem RecursiveIn_cond_core_rfind {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f g : ℕ →. ℕ} (hc : Computable c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    ∃ cmp : ℕ →. ℕ, RecursiveIn O cmp ∧
      (fun n => Nat.rfind (fun k => (fun m => m = 0) <$> cmp (Nat.pair n k))) =
        (fun n => cond (c n) (f n) (g n)) := by
  classical
  -- Definitions following the informal proof
  let eqF : ℕ →. ℕ := fun p =>
    ((Nat.pair <$> ((fun n : ℕ => (Nat.unpair n).1) p >>= f) <*> (fun n : ℕ => (Nat.unpair n).2) p) >>= eq01)
  let eqG : ℕ →. ℕ := fun p =>
    ((Nat.pair <$> ((fun n : ℕ => (Nat.unpair n).1) p >>= g) <*> (fun n : ℕ => (Nat.unpair n).2) p) >>= eq01)
  let c1 : ℕ → Bool := fun p => c (Nat.unpair p).1
  let c2 : ℕ → Bool := fun p => !c (Nat.unpair p).1

  have hc1 : Computable c1 := by
    have hleft : Computable (fun p : ℕ => (Nat.unpair p).1) := (Computable.fst.comp Computable.unpair)
    simpa [c1] using hc.comp hleft
  have hc2 : Computable c2 := by
    have hnot : Computable not := Primrec.not.to_comp
    simpa [c2] using hnot.comp hc1

  have heqF : RecursiveIn O eqF := by
    have hf_left : RecursiveIn O (fun p => (fun n : ℕ => (Nat.unpair n).1) p >>= f) :=
      RecursiveIn.comp hf (RecursiveIn.left)
    have hright : RecursiveIn O (fun p => (Nat.unpair p).2) := RecursiveIn.right
    have hpair : RecursiveIn O (fun p => Nat.pair <$> ((fun n : ℕ => (Nat.unpair n).1) p >>= f) <*> (fun p => (Nat.unpair p).2) p) :=
      RecursiveIn.pair hf_left hright
    have : RecursiveIn O (fun p => (Nat.pair <$> ((fun n : ℕ => (Nat.unpair n).1) p >>= f) <*> (fun p => (Nat.unpair p).2) p) >>= eq01) :=
      RecursiveIn.comp (eq01_recursiveIn O) hpair
    simpa [eqF] using this
  have heqG : RecursiveIn O eqG := by
    have hg_left : RecursiveIn O (fun p => (fun n : ℕ => (Nat.unpair n).1) p >>= g) :=
      RecursiveIn.comp hg (RecursiveIn.left)
    have hright : RecursiveIn O (fun p => (Nat.unpair p).2) := RecursiveIn.right
    have hpair : RecursiveIn O (fun p => Nat.pair <$> ((fun n : ℕ => (Nat.unpair n).1) p >>= g) <*> (fun p => (Nat.unpair p).2) p) :=
      RecursiveIn.pair hg_left hright
    have : RecursiveIn O (fun p => (Nat.pair <$> ((fun n : ℕ => (Nat.unpair n).1) p >>= g) <*> (fun p => (Nat.unpair p).2) p) >>= eq01) :=
      RecursiveIn.comp (eq01_recursiveIn O) hpair
    simpa [eqG] using this

  let t1 : ℕ →. ℕ := fun p => bif c1 p then eqF p else Part.some 1
  let t2 : ℕ →. ℕ := fun p => bif c2 p then eqG p else Part.some 1

  have ht1 : RecursiveIn O t1 := by
    simpa [t1] using (RecursiveIn_cond_const (O := O) (c := c1) (f := eqF) hc1 heqF 1)
  have ht2 : RecursiveIn O t2 := by
    simpa [t2] using (RecursiveIn_cond_const (O := O) (c := c2) (f := eqG) hc2 heqG 1)

  -- Lift a computation recursive in the empty oracle set to any oracle set.
  have lift_empty : ∀ {h : ℕ →. ℕ}, RecursiveIn ({} : Set (ℕ →. ℕ)) h → RecursiveIn O h := by
    intro h hh
    induction hh with
    | zero => exact RecursiveIn.zero
    | succ => exact RecursiveIn.succ
    | left => exact RecursiveIn.left
    | right => exact RecursiveIn.right
    | oracle g hg => cases hg
    | pair _ _ ih1 ih2 => exact RecursiveIn.pair ih1 ih2
    | comp _ _ ih1 ih2 => exact RecursiveIn.comp ih1 ih2
    | prec _ _ ih1 ih2 => exact RecursiveIn.prec ih1 ih2
    | rfind _ ih => exact RecursiveIn.rfind ih

  let mulPair : ℕ →. ℕ := (Nat.unpaired (fun a b : ℕ => a * b) : ℕ → ℕ)
  have hmul : RecursiveIn O mulPair := by
    have hpart : Nat.Partrec (mulPair : ℕ →. ℕ) := by
      simpa [mulPair] using (Nat.Partrec.of_primrec (Nat.Primrec.mul))
    have h0 : RecursiveIn ({} : Set (ℕ →. ℕ)) (mulPair : ℕ →. ℕ) :=
      (recursiveIn_empty_iff_partrec (f := (mulPair : ℕ →. ℕ))).2 hpart
    exact lift_empty h0

  let cmp : ℕ →. ℕ := fun p => (Nat.pair <$> t1 p <*> t2 p) >>= mulPair
  have hcmp : RecursiveIn O cmp := by
    have hpair : RecursiveIn O (fun p => Nat.pair <$> t1 p <*> t2 p) :=
      RecursiveIn.pair ht1 ht2
    have : RecursiveIn O (fun p => (Nat.pair <$> t1 p <*> t2 p) >>= mulPair) :=
      RecursiveIn.comp hmul hpair
    simpa [cmp] using this

  refine ⟨cmp, hcmp, ?_⟩
  funext n
  let φ : ℕ → Bool := fun m => decide (m = 0)
  cases hn : c n with
  | true =>
      simp [_root_.cond]
      have hpred : (fun k => Part.map φ (cmp (Nat.pair n k))) =
          (fun k => Part.map φ (((Nat.pair <$> f n <*> Part.some k) >>= eq01))) := by
        funext k
        have hcmpk : cmp (Nat.pair n k) = ((Nat.pair <$> f n <*> Part.some k) >>= eq01) := by
          simp [cmp, t1, t2, c1, c2, eqF, eqG, mulPair, hn, Nat.unpair_pair, Nat.unpaired,
            Seq.seq, Part.bind_assoc, Part.bind_some, Part.bind_some_right]
        simp [hcmpk]
      rw [hpred]
      exact eq01_rfind (v := f n)
  | false =>
      simp [_root_.cond]
      have hpred : (fun k => Part.map φ (cmp (Nat.pair n k))) =
          (fun k => Part.map φ (((Nat.pair <$> g n <*> Part.some k) >>= eq01))) := by
        funext k
        have hcmpk : cmp (Nat.pair n k) = ((Nat.pair <$> g n <*> Part.some k) >>= eq01) := by
          simp [cmp, t1, t2, c1, c2, eqF, eqG, mulPair, hn, Nat.unpair_pair, Nat.unpaired,
            Seq.seq, Part.bind_assoc, Part.bind_some, Part.bind_some_right]
        simp [hcmpk]
      rw [hpred]
      exact eq01_rfind (v := g n)


theorem RecursiveIn_cond {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f g : ℕ →. ℕ}
    (hc : Computable c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O (fun n => cond (c n) (f n) (g n)) := by
  classical
  rcases RecursiveIn_cond_core_rfind (O := O) (c := c) (f := f) (g := g) hc hf hg with ⟨cmp, hcmp, hEq⟩
  have hr : RecursiveIn O (fun n => Nat.rfind (fun k => (fun m => m = 0) <$> cmp (Nat.pair n k))) := by
    exact RecursiveIn.rfind hcmp
  refine RecursiveIn.of_eq hr ?_
  intro n
  simpa using congrArg (fun h => h n) hEq


theorem RecursiveIn_subst {O O' : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} (hf : RecursiveIn O f)
    (hO : ∀ g, g ∈ O → RecursiveIn O' g) : RecursiveIn O' f := by
  induction hf with
  | zero =>
      simpa using (RecursiveIn.zero (O := O'))
  | succ =>
      simpa using (RecursiveIn.succ (O := O'))
  | left =>
      simpa using (RecursiveIn.left (O := O'))
  | right =>
      simpa using (RecursiveIn.right (O := O'))
  | oracle g hg =>
      exact hO g hg
  | pair hf hg ihf ihg =>
      exact RecursiveIn.pair ihf ihg
  | comp hf hg ihf ihg =>
      exact RecursiveIn.comp ihf ihg
  | prec hf hg ihf ihg =>
      exact RecursiveIn.prec ihf ihg
  | rfind hf ihf =>
      exact RecursiveIn.rfind ihf

theorem turingJoin_recursiveIn_pair (f g : ℕ →. ℕ) : RecursiveIn ({f, g} : Set (ℕ →. ℕ)) (f ⊕ g) := by
  let O : Set (ℕ →. ℕ) := ({f, g} : Set (ℕ →. ℕ))

  let payload : ℕ →. ℕ := fun n => (Nat.div2 n : ℕ)
  let dbl : ℕ →. ℕ := fun n => (2 * n : ℕ)
  let dbl1 : ℕ →. ℕ := fun n => (2 * n + 1 : ℕ)

  have hpayload : RecursiveIn O payload := by
    refine RecursiveIn.of_primrec (O := O) ?_
    exact (Primrec.nat_iff.1 (by simpa using (Primrec.nat_div2 : Primrec Nat.div2)))

  have hdbl : RecursiveIn O dbl := by
    refine RecursiveIn.of_primrec (O := O) ?_
    have hprim : Primrec (fun n : ℕ => 2 * n) :=
      Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
    exact (Primrec.nat_iff.1 hprim)

  have hdbl1 : RecursiveIn O dbl1 := by
    refine RecursiveIn.of_primrec (O := O) ?_
    have hprim : Primrec (fun n : ℕ => 2 * n + 1) :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
        (Primrec.const 1)
    exact (Primrec.nat_iff.1 hprim)

  have hfO : RecursiveIn O f := RecursiveIn.oracle f (by simp [O])
  have hgO : RecursiveIn O g := RecursiveIn.oracle g (by simp [O])

  let evenBranch : ℕ →. ℕ := fun n => (payload n >>= f) >>= dbl
  let oddBranch : ℕ →. ℕ := fun n => (payload n >>= g) >>= dbl1

  have heven : RecursiveIn O evenBranch := by
    have h1 : RecursiveIn O (fun n => payload n >>= f) := RecursiveIn.comp hfO hpayload
    have h2 : RecursiveIn O (fun n => (payload n >>= f) >>= dbl) := RecursiveIn.comp hdbl h1
    simpa [evenBranch] using h2

  have hodd : RecursiveIn O oddBranch := by
    have h1 : RecursiveIn O (fun n => payload n >>= g) := RecursiveIn.comp hgO hpayload
    have h2 : RecursiveIn O (fun n => (payload n >>= g) >>= dbl1) := RecursiveIn.comp hdbl1 h1
    simpa [oddBranch] using h2

  have hc : Computable Nat.bodd := by
    simpa using (Computable.nat_bodd : Computable Nat.bodd)

  have hcond :
      RecursiveIn O (fun n => cond (Nat.bodd n) (oddBranch n) (evenBranch n)) :=
    RecursiveIn_cond (O := O) (c := Nat.bodd) (f := oddBranch) (g := evenBranch) hc hodd heven

  refine (RecursiveIn.of_eq (O := O) hcond ?_)
  intro n
  cases hb : Nat.bodd n with
  | false =>
      have hdn : Denumerable.ofNat (ℕ ⊕ ℕ) n = Sum.inl n.div2 := by
        refine Denumerable.ofNat_of_decode (α := ℕ ⊕ ℕ) (n := n) (b := Sum.inl n.div2) ?_
        simp [-Denumerable.decode_eq_ofNat, Encodable.decode_sum_val, Encodable.decodeSum,
          Nat.boddDiv2_eq, hb]
      simp [turingJoin, liftPrimcodable, gjoin, payload, dbl, dbl1, evenBranch, oddBranch,
        hdn, Part.bind_some_eq_map, Part.map_map]
      have hfun : (encode ∘ fun b : ℕ => (Sum.inl b : ℕ ⊕ ℕ)) = (HMul.hMul 2) := by
        funext b
        simp [Function.comp]
      simp [hfun]
  | true =>
      have hdn : Denumerable.ofNat (ℕ ⊕ ℕ) n = Sum.inr n.div2 := by
        refine Denumerable.ofNat_of_decode (α := ℕ ⊕ ℕ) (n := n) (b := Sum.inr n.div2) ?_
        simp [-Denumerable.decode_eq_ofNat, Encodable.decode_sum_val, Encodable.decodeSum,
          Nat.boddDiv2_eq, hb]
      simp [turingJoin, liftPrimcodable, gjoin, payload, dbl, dbl1, evenBranch, oddBranch,
        hdn, Part.bind_some_eq_map, Part.map_map]
      have hfun : (encode ∘ fun b : ℕ => (Sum.inr b : ℕ ⊕ ℕ)) = (fun y : ℕ => 2 * y + 1) := by
        funext b
        simp [Function.comp]
      simp [hfun]


theorem join_le (f g h : ℕ →. ℕ) (hf : TuringReducible f h) (hg : TuringReducible g h) : TuringReducible (f ⊕ g) h := by
  unfold TuringReducible at *
  have hj : RecursiveIn ({f, g} : Set (ℕ →. ℕ)) (f ⊕ g) := turingJoin_recursiveIn_pair f g
  have hO : ∀ k, k ∈ ({f, g} : Set (ℕ →. ℕ)) → RecursiveIn ({h} : Set (ℕ →. ℕ)) k := by
    intro k hk
    have hk' : k = f ∨ k = g := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hk
    cases hk' with
    | inl hkf =>
        simpa [hkf] using hf
    | inr hkg =>
        simpa [hkg] using hg
  exact RecursiveIn_subst (O := ({f, g} : Set (ℕ →. ℕ))) (O' := ({h} : Set (ℕ →. ℕ))) (f := (f ⊕ g)) hj hO


/-!
## Semilattice Structure on Turing Degrees

We show that `turingJoin` respects Turing equivalence and lifts to a supremum operation
on `TuringDegree`, making it a `SemilatticeSup`.
-/

namespace TuringDegree

/-- The Turing join respects Turing reducibility: if `f ≤ᵀ f'` and `g ≤ᵀ g'`,
then `f ⊕ g ≤ᵀ f' ⊕ g'`. -/
theorem join_mono {f f' g g' : ℕ →. ℕ} (hf : f ≤ᵀ f') (hg : g ≤ᵀ g') :
    (f ⊕ g) ≤ᵀ (f' ⊕ g') := by
  have hf' : f ≤ᵀ (f' ⊕ g') := hf.trans (left_le_join f' g')
  have hg' : g ≤ᵀ (f' ⊕ g') := hg.trans (right_le_join f' g')
  exact join_le f g (f' ⊕ g') hf' hg'

/-- The Turing join respects Turing equivalence. -/
theorem join_congr {f f' g g' : ℕ →. ℕ} (hf : f ≡ᵀ f') (hg : g ≡ᵀ g') :
    (f ⊕ g) ≡ᵀ (f' ⊕ g') :=
  ⟨join_mono hf.1 hg.1, join_mono hf.2 hg.2⟩

/-- The supremum operation on Turing degrees, induced by the Turing join. -/
def sup : TuringDegree → TuringDegree → TuringDegree :=
  Quotient.lift₂
    (fun f g => toAntisymmetrization TuringReducible (f ⊕ g))
    (fun _ _ _ _ hf hg => Quotient.sound (join_congr hf hg))

theorem sup_mk (f g : ℕ →. ℕ) :
    TuringDegree.sup (toAntisymmetrization TuringReducible f) (toAntisymmetrization TuringReducible g) =
    toAntisymmetrization TuringReducible (f ⊕ g) := rfl

theorem le_sup_left (a b : TuringDegree) : a ≤ TuringDegree.sup a b := by
  induction a using Quotient.inductionOn'
  induction b using Quotient.inductionOn'
  exact left_le_join _ _

theorem le_sup_right (a b : TuringDegree) : b ≤ TuringDegree.sup a b := by
  induction a using Quotient.inductionOn'
  induction b using Quotient.inductionOn'
  exact right_le_join _ _

theorem sup_le {a b c : TuringDegree} (ha : a ≤ c) (hb : b ≤ c) :
    TuringDegree.sup a b ≤ c := by
  induction a using Quotient.inductionOn'
  induction b using Quotient.inductionOn'
  induction c using Quotient.inductionOn'
  exact join_le _ _ _ ha hb

instance instSemilatticeSup : SemilatticeSup TuringDegree where
  sup := sup
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le _ _ _ := sup_le

/-- The sup on Turing degrees agrees with the Turing join on representatives. -/
@[simp]
lemma sup_def (f g : ℕ →. ℕ) :
    (toAntisymmetrization TuringReducible f) ⊔ (toAntisymmetrization TuringReducible g) =
    toAntisymmetrization TuringReducible (f ⊕ g) := rfl

end TuringDegree
