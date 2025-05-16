import Computability.TuringDegree
import Mathlib.Data.Option.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.PSub
import Mathlib.Data.PFun
import Mathlib.Data.Part

open Denumerable Encodable
-- This section provides and encoding for oracle partial recursive functions and a definition
-- of the universal partial recursive function relative to an oracle, along with a proof that it is universal.

variable {α : Type} [Denumerable α]

theorem RecursiveIn.rfind' {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
  RecursiveIn O (Nat.unpaired fun a m =>
    (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m))
  := by sorry

def oracleCode (f : α → ℕ →. ℕ) : ℕ → ℕ →. ℕ :=
  λ i n => match decode i with
           | some a => f a n
           | none   => ⊥

inductive codeo : Type
| zero : codeo
| succ : codeo
| left : codeo
| right : codeo
| oracle : ℕ → codeo
| pair : codeo → codeo → codeo
| comp : codeo → codeo → codeo
| prec : codeo → codeo → codeo
| rfind' : codeo → codeo


/-- Semantics of `codeo`, relative to an indexed oracle family. -/
def evalo {α : Type} [Primcodable α] (f : α → ℕ →. ℕ) : codeo → ℕ →. ℕ
| codeo.zero => pure 0
| codeo.succ => fun n => some (n + 1)
| codeo.left => fun n => some (Nat.unpair n).1
| codeo.right => fun n => some (Nat.unpair n).2
| codeo.oracle i =>
    match decode i with
    | some a => f a
    | none   => λ n => ⊥
| codeo.pair cf cg =>
    fun n => Nat.pair <$> evalo f cf n <*> evalo f cg n
| codeo.comp cf cg =>
    fun n => evalo f cg n >>= evalo f cf
| codeo.prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (evalo f cf a) fun y IH => do
        let i ← IH
        evalo f cg (Nat.pair a (Nat.pair y i))
| codeo.rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun x => x = 0) <$> evalo f cf (Nat.pair a (n + m))).map (· + m)

def encodeCodeo : codeo → ℕ
| codeo.zero        => 0
| codeo.succ        => 1
| codeo.left        => 2
| codeo.right       => 3
| codeo.oracle i    => 8 * i + 4
| codeo.pair cf cg  => 8 * Nat.pair (encodeCodeo cf) (encodeCodeo cg) + 5
| codeo.comp cf cg  => 8 * Nat.pair (encodeCodeo cf) (encodeCodeo cg) + 6
| codeo.prec cf cg  => 8 * Nat.pair (encodeCodeo cf) (encodeCodeo cg) + 7
| codeo.rfind' cf   => 8 * encodeCodeo cf + 8  -- tag 0 mod 8 but ≥ 8


def decodeCodeo : ℕ → codeo
  | 0 => codeo.zero
  | 1 => codeo.succ
  | 2 => codeo.left
  | 3 => codeo.right
  | 4 => codeo.oracle 0
  | n + 5 =>
    let m := (n + 5) / 8
    have hm : m < n + 5 := by
      apply Nat.div_lt_self
      · linarith       -- n + 5 > 0
      · decide         -- 8 > 1
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    match (n + 5) % 8 with
    | 0 => codeo.rfind' (decodeCodeo m)
    | 4 => codeo.oracle m
    | 5 => codeo.pair (decodeCodeo m.unpair.1) (decodeCodeo m.unpair.2)
    | 6 => codeo.comp (decodeCodeo m.unpair.1) (decodeCodeo m.unpair.2)
    | 7 => codeo.prec (decodeCodeo m.unpair.1) (decodeCodeo m.unpair.2)
    | _ => codeo.zero  -- dummy value; unreachable if `encodeCodeo` used properly


theorem encodeCodeo_decodeCodeo : ∀ c, encodeCodeo (decodeCodeo c) = c :=
λ c => match c with
  | 0 => by simp [decodeCodeo, encodeCodeo]
  | 1 => by simp [decodeCodeo, encodeCodeo]
  | 2 => by simp [decodeCodeo, encodeCodeo]
  | 3 => by simp [decodeCodeo, encodeCodeo]
  | 4 => by simp [decodeCodeo, encodeCodeo]
  | n + 5 => by {
    let m := (n + 5) / 8
    have hm : m < n + 5 := by
      apply Nat.div_lt_self
      · linarith       -- n + 5 > 0
      · decide         -- 8 > 1
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encodeCodeo_decodeCodeo m
    have IH₁ := encodeCodeo_decodeCodeo m.unpair.1
    have IH₂ := encodeCodeo_decodeCodeo m.unpair.2
    sorry
  }

/-- Returns a code for the constant function outputting a particular natural. -/
def const : ℕ → codeo
  | 0 => codeo.zero
  | n + 1 => codeo.comp codeo.succ (const n)

def const_inj : ∀ {n₁ n₂}, const n₁ = const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

/-- A code for the identity function. -/
def id_code : codeo :=
  codeo.pair codeo.left codeo.right

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : codeo) (n : ℕ) : codeo :=
  codeo.comp c (codeo.pair (const n) id_code)

-- -- helper lemma to prove rfind' case of univ theorem, since rfind' is defined differently from rfind
theorem rfind'o {α : Type} [Primcodable α] {g : α → ℕ →. ℕ} {cf : codeo}
    (hf : RecursiveIn (Set.range g) (evalo g cf)) :
  RecursiveIn (Set.range g)
    (Nat.unpaired fun a m =>
      (Nat.rfind fun n =>
        (fun m => m = 0) <$> evalo g cf (Nat.pair a (n + m))
      ).map (· + m))
 := sorry

/-- A function is partial recursive relative to an indexed set of oracles `O` if and only if there is a code implementing it.
Therefore, `evalo` is a **universal partial recursive function relative to `g`**. -/
theorem exists_code_rel {α : Type} [Primcodable α] (g : α → ℕ →. ℕ) (f : ℕ →. ℕ) :
  RecursiveIn (Set.range g) f ↔ ∃ c : codeo, evalo g c = f := by
  constructor
  · intro gf
    induction gf
    · exact ⟨codeo.zero, rfl⟩
    · exact ⟨codeo.succ, rfl⟩
    · exact ⟨codeo.left, rfl⟩
    · exact ⟨codeo.right, rfl⟩
    · case mp.oracle hf =>
      rcases hf with ⟨cf, rfl⟩
      exact ⟨codeo.oracle (encode cf), by
        funext n
        simp only [evalo, codeo.oracle]
        rw [encodek]⟩
    · case mp.pair hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.pair cf cg, rfl⟩
    · case mp.comp hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.comp cf cg, rfl⟩
    · case mp.prec hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.prec cf cg, rfl⟩
    · case mp.rfind f' pf hf =>
      rcases hf with ⟨cg, h⟩
      use (cg.rfind'.comp (id_code.pair codeo.zero))
      simp [evalo]
      sorry
  · rintro ⟨c, rfl⟩
    induction c with
    | zero =>
      exact RecursiveIn.zero
    | succ =>
      exact RecursiveIn.succ
    | left =>
      exact RecursiveIn.left
    | right =>
      exact RecursiveIn.right
    | oracle i =>
      cases h : decode (α := α) i with
      | some a =>
        apply RecursiveIn.of_eq (RecursiveIn.oracle (g a) (Set.mem_range_self _))
        intro n
        simp [evalo, h]
      | none =>
        apply RecursiveIn.of_eq RecursiveIn.none
        intro n
        simp [evalo, h]
        rfl
    | pair cf cg pf pg =>
      exact pf.pair pg
    | comp cf cg pf pg =>
      apply RecursiveIn.comp
      exact pf
      exact pg
    | prec cf cg pf pg =>
      apply RecursiveIn.prec
      exact pf
      exact pg
    | rfind' cf pf =>
      apply rfind'o
      exact pf
