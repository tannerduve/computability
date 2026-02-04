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

theorem RecursiveIn_cond {O : Set (ℕ →. ℕ)} {c : ℕ → Bool} {f g : ℕ →. ℕ}
    (hc : Computable c) (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O (fun n => cond (c n) (f n) (g n)) := by
  let eq01 : ℕ →. ℕ := fun p => if (Nat.unpair p).1 = (Nat.unpair p).2 then 0 else 1
  have hComp : Computable (fun p : ℕ => if (Nat.unpair p).1 = (Nat.unpair p).2 then 0 else 1) := by
    have hDec : Computable (fun p : ℕ => decide ((Nat.unpair p).1 = (Nat.unpair p).2)) := by
      have hDec2 : Computable (fun q : ℕ × ℕ => decide (q.1 = q.2)) := by
        simpa using ((Primrec.eq (α := ℕ)).decide : Primrec₂ (fun a b : ℕ => decide (a = b))).to_comp
      simpa [Function.comp] using hDec2.comp (Computable.unpair)
    have h0 : Computable (fun _ : ℕ => (0:ℕ)) := Computable.const 0
    have h1 : Computable (fun _ : ℕ => (1:ℕ)) := Computable.const 1
    sorry
  have hPart : _root_.Partrec (fun p : ℕ => if (Nat.unpair p).1 = (Nat.unpair p).2 then 0 else 1 : ℕ →. ℕ) :=
    sorry
  have hNatPart : Nat.Partrec eq01 := (Partrec.nat_iff).1 hPart
  sorry

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
        hb, hdn, O, Part.bind_some_eq_map, Part.map_map]
      have hfun : (encode ∘ fun b : ℕ => (Sum.inl b : ℕ ⊕ ℕ)) = (HMul.hMul 2) := by
        funext b
        simp [Function.comp]
      simpa [hfun]
  | true =>
      have hdn : Denumerable.ofNat (ℕ ⊕ ℕ) n = Sum.inr n.div2 := by
        refine Denumerable.ofNat_of_decode (α := ℕ ⊕ ℕ) (n := n) (b := Sum.inr n.div2) ?_
        simp [-Denumerable.decode_eq_ofNat, Encodable.decode_sum_val, Encodable.decodeSum,
          Nat.boddDiv2_eq, hb]
      simp [turingJoin, liftPrimcodable, gjoin, payload, dbl, dbl1, evenBranch, oddBranch,
        hb, hdn, O, Part.bind_some_eq_map, Part.map_map]
      have hfun : (encode ∘ fun b : ℕ => (Sum.inr b : ℕ ⊕ ℕ)) = (fun y : ℕ => 2 * y + 1) := by
        funext b
        simp [Function.comp]
      simpa [hfun]


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

def TuringDegree.add (a b : TuringDegree) : TuringDegree :=
  Quotient.liftOn₂ a b (fun f g => ⟦f ⊕ g⟧)
    (by {
      intro f₁ f₂ g₁ g₂ hf hg
      apply Quot.sound
      simp [AntisymmRel, TuringReducible]
      constructor
      cases' hf with hf₁ hf₂
      cases' hg with hg₁ hg₂
      all_goals {sorry}
    })
