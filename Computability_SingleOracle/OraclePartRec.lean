/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
import Mathlib.Computability.Partrec
import Mathlib.Order.Antisymmetrization

/-!
# Oracle Computability

This file defines a model of oracle computability using partial recursive functions. It extends
the notion of `Nat.Partrec` by allowing access to a set of oracle functions.

## Main Definitions

* `RecursiveIn O f`:
  A partial function `f : ℕ →. ℕ` is recursive in a set of oracles `O ⊆ ℕ →. ℕ` if it can be
  constructed from constants, basic operations, and functions in `O` using pairing, composition,
  primitive recursion, and μ-recursion.
* `liftPrim`: Encodes a function `α →. σ` as a function `ℕ →. ℕ` using `Primcodable`.
* `RecursiveIn'`, `RecursiveIn₂`, `ComputableIn`, `ComputableIn₂`:
  Versions of `RecursiveIn` for functions between `Primcodable` types.

## Implementation Notes

The encoding/decoding mechanism relies on `Primcodable`. The definition of `RecursiveIn` mimics
the inductive structure of `Nat.Partrec`.

## References

* [Odifreddi1989] Odifreddi, Piergiorgio.
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers*, Vol. I.

## Tags

Computability, Oracle, Recursion, Primitive Recursion
-/

open Primrec Nat.Partrec Part Encodable

variable {f g h : ℕ →. ℕ}

/--
The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.
-/
inductive RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop
  | zero : RecursiveIn O fun _ => 0
  | succ : RecursiveIn O Nat.succ
  | left : RecursiveIn O fun n => (Nat.unpair n).1
  | right : RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : ∀ g ∈ O, RecursiveIn O g
  | pair {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun n => h n >>= f
  | prec {f h : ℕ →. ℕ} (hf : RecursiveIn O f) (hh : RecursiveIn O h) :
      RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
      RecursiveIn O fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)

def liftPrim {α σ} [Primcodable α] [Primcodable σ] (f : α →. σ) : ℕ →. ℕ :=
  fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

def RecursiveIn' {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α →. σ) : Prop :=
  RecursiveIn O (liftPrim f)

/-- A binary partial function is recursive in `O` if the curried form is. -/
def RecursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β →. σ) : Prop :=
  RecursiveIn' O (fun p : α × β => f p.1 p.2)

/-- A total function is computable in `O` if its constant lift is recursive in `O`. -/
def ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (ℕ →. ℕ)) (f : α → σ) : Prop :=
  RecursiveIn' O (fun a => Part.some (f a))

/-- A binary total function is computable in `O`. -/
def ComputableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (ℕ →. ℕ)) (f : α → β → σ) : Prop :=
  ComputableIn O (fun p : α × β => f p.1 p.2)

theorem RecursiveIn.of_eq {f g : ℕ →. ℕ} (hf : RecursiveIn O f) (H : ∀ n, f n = g n) :
    RecursiveIn O g :=
  (funext H : f = g) ▸ hf

theorem RecursiveIn.of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ} (hf : RecursiveIn O f)
    (H : ∀ n, g n ∈ f n) : RecursiveIn O g :=
  hf.of_eq fun n => eq_some_iff.2 (H n)

/--
If a function is partial recursive, then it is recursive in every partial function.
-/
lemma Nat.Partrec.recursiveIn (pF : Nat.Partrec f) : RecursiveIn O f := by
  induction' pF with f' g' _ _ ih₁ ih₂ f' g' _ _ ih₁ ih₂ f' g' _ _ ih₁ ih₂ f' _ ih
  repeat {constructor}
  · case pair =>
    apply RecursiveIn.pair ih₁ ih₂
  · case comp =>
    apply RecursiveIn.comp ih₁ ih₂
  · case prec =>
    apply RecursiveIn.prec ih₁ ih₂
  · case rfind =>
    apply RecursiveIn.rfind ih

/--
If a function is computable, then it is computable in every oracle.
-/
theorem Computable.computableIn {f : α → β} [Primcodable α]
[Primcodable β]
(hf : Computable f) : ComputableIn O f :=
  Nat.Partrec.recursiveIn (by simpa [Computable] using hf)

theorem RecursiveIn.of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
RecursiveIn O (fun n => f n) := Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)

theorem Primrec.to_computableIn {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} (hf : Primrec f) (O : Set (ℕ →. ℕ)) :
    ComputableIn O f := Computable.computableIn (Primrec.to_comp hf)

nonrec theorem Primrec₂.to_computableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} (hf : Primrec₂ f) (O : Set (ℕ →. ℕ)) :
    ComputableIn₂ O f :=
  Primrec.to_computableIn hf O

protected theorem ComputableIn.recursiveIn' {α σ} [Primcodable α] [Primcodable σ]
    {f : α → σ} {O} (hf : ComputableIn O f) :
    RecursiveIn' O (fun a => Part.some (f a)) := hf

protected theorem ComputableIn₂.recursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → β → σ} {O} (hf : ComputableIn₂ O f) :
    RecursiveIn₂ O fun a => (f a : β →. σ) := hf

protected theorem RecursiveIn.some : RecursiveIn O some :=
  RecursiveIn.of_primrec Nat.Primrec.id

theorem RecursiveIn.none : RecursiveIn O (fun _ => none) :=
  (RecursiveIn.of_primrec (Nat.Primrec.const 1)).rfind.of_eq fun _ =>
    eq_none_iff.2 fun _ ⟨h, _⟩ => by simp at h

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem const_in (O : Set (ℕ →. ℕ)) (s : σ) : ComputableIn O (fun _ : α => s) :=
  Primrec.to_computableIn (Primrec.const s) O

theorem id_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@id α) :=
  Primrec.to_computableIn Primrec.id O

theorem fst_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.fst α β) :=
  Primrec.to_computableIn Primrec.fst O

theorem snd_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Prod.snd α β) :=
  Primrec.to_computableIn Primrec.snd O

theorem unpair_in (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.unpair :=
  Primrec.to_computableIn Primrec.unpair O

theorem succ_in (O : Set (ℕ →. ℕ)) : ComputableIn O Nat.succ :=
  Primrec.to_computableIn Primrec.succ O

theorem sumInl_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inl α β) :=
  Primrec.to_computableIn Primrec.sumInl O

theorem sumInr_in (O : Set (ℕ →. ℕ)) : ComputableIn O (@Sum.inr α β) :=
  Primrec.to_computableIn Primrec.sumInr O

/--
If a function is recursive in the constant zero function,
then it is partial recursive.
-/
lemma RecursiveIn.partrec_of_zero (fRecInZero : RecursiveIn {fun _ => Part.some 0} f) : Nat.Partrec f := by
  induction' fRecInZero with g hg g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g _ ih
  repeat {constructor}
  · rw [Set.mem_singleton_iff] at hg; rw [hg];
    exact Nat.Partrec.zero
  repeat {constructor; assumption; try assumption}

/--
If a function is partial recursive in the constant none function,
then it is partial recursive.
-/
lemma RecursiveIn.partrec_of_none (fRecInNone : RecursiveIn {fun _ => Part.none} f) : Nat.Partrec f := by
  induction' fRecInNone with g hg g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g _ ih
  repeat {constructor}
  · rw [Set.mem_singleton_iff] at hg; rw [hg];
    exact Nat.Partrec.none
  repeat {constructor; assumption; try assumption}

/--
A partial function `f` is partial recursive if and only if it is recursive in
every partial function `g`.
-/
theorem partrec_iff_forall_recursiveIn : Nat.Partrec f ↔ ∀ g, RecursiveIn {g} f:=
  ⟨fun hf _ ↦ hf.recursiveIn, (· _ |>.partrec_of_zero)⟩

@[simp] lemma recursiveIn_empty_iff_partrec : RecursiveIn {} f ↔ Nat.Partrec f  where
  mp fRecInNone := by
    induction' fRecInNone with g hg g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g h _ _ ih₁ ih₂ g _ ih
    repeat {constructor}
    · simp at hg
    repeat {constructor; assumption; try assumption}
  mpr pF := by
    induction' pF with f' g' _ _ ih₁ ih₂ f' g' _ _ ih₁ ih₂ f' g' _ _ ih₁ ih₂ f' _ ih
    repeat {constructor}
    · case pair =>
      apply RecursiveIn.pair ih₁ ih₂
    · case comp =>
      apply RecursiveIn.comp ih₁ ih₂
    · case prec =>
      apply RecursiveIn.prec ih₁ ih₂
    · case rfind =>
      apply RecursiveIn.rfind ih
