import Computability.SingleOracle.TuringDegree
import Mathlib.Data.Option.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.PSub
import Mathlib.Data.PFun
import Mathlib.Data.Part

import Mathlib.Computability.PartrecCode

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
| oracle : codeo
| pair : codeo → codeo → codeo
| comp : codeo → codeo → codeo
| prec : codeo → codeo → codeo
| rfind' : codeo → codeo

-- instance Primcodable.codeo : Primcodable codeo := by
--   exact?


/-- Semantics of `codeo`, relative to an indexed oracle family. -/
def evalo (O : ℕ →. ℕ) : codeo → ℕ →. ℕ
| codeo.zero => pure 0
| codeo.succ => fun n => some (n + 1)
| codeo.left => fun n => some (Nat.unpair n).1
| codeo.right => fun n => some (Nat.unpair n).2
| codeo.oracle => O
| codeo.pair cf cg =>
    fun n => Nat.pair <$> evalo O cf n <*> evalo O cg n
| codeo.comp cf cg =>
    fun n => evalo O cg n >>= evalo O cf
| codeo.prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (evalo O cf a) fun y IH => do
        let i ← IH
        evalo O cg (Nat.pair a (Nat.pair y i))
| codeo.rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun x => x = 0) <$> evalo O cf (Nat.pair a (n + m))).map (· + m)

def encodeCodeo : codeo → ℕ
| codeo.zero        => 0
| codeo.succ        => 1
| codeo.left        => 2
| codeo.right       => 3
| codeo.oracle      => 4
| codeo.pair cf cg  => 8 * Nat.pair (encodeCodeo cf) (encodeCodeo cg) + 5
| codeo.comp cf cg  => 8 * Nat.pair (encodeCodeo cf) (encodeCodeo cg) + 6
| codeo.prec cf cg  => 8 * Nat.pair (encodeCodeo cf) (encodeCodeo cg) + 7
| codeo.rfind' cf   => 8 * encodeCodeo cf + 8  -- tag 0 mod 8 but ≥ 8


def decodeCodeo : ℕ → codeo
  | 0 => codeo.zero
  | 1 => codeo.succ
  | 2 => codeo.left
  | 3 => codeo.right
  | 4 => codeo.oracle
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
    | 4 => codeo.oracle
    | 5 => codeo.pair (decodeCodeo m.unpair.1) (decodeCodeo m.unpair.2)
    | 6 => codeo.comp (decodeCodeo m.unpair.1) (decodeCodeo m.unpair.2)
    | 7 => codeo.prec (decodeCodeo m.unpair.1) (decodeCodeo m.unpair.2)
    | _ => codeo.zero  -- dummy value?

instance : OfNat (codeo) m where ofNat := decodeCodeo m
instance : Coe (ℕ) (codeo) := ⟨decodeCodeo⟩

/-- Converts an `codeo` into a `ℕ`. -/
@[coe]
def ofcodeo : codeo → ℕ := encodeCodeo

@[simp] theorem decodeCodeo_encodeCodeo : ∀ c, decodeCodeo (encodeCodeo c) = c := by sorry

@[simp] theorem encodeCodeo_decodeCodeo : ∀ c, encodeCodeo (decodeCodeo c) = c :=
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
def codeo_const : ℕ → codeo
  | 0 => codeo.zero
  | n + 1 => codeo.comp codeo.succ (codeo_const n)

def const_inj : ∀ {n₁ n₂}, codeo_const n₁ = codeo_const n₂ → n₁ = n₂
  | 0, 0, _ => by simp
  | n₁ + 1, n₂ + 1, h => by
    dsimp [codeo_const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

theorem evalo_const (g : ℕ →. ℕ) : evalo g (codeo_const a) _b = a := by sorry

/-- A code for the identity function. -/
def id_code : codeo :=
  codeo.pair codeo.left codeo.right

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : codeo) (n : ℕ) : codeo :=
  codeo.comp c (codeo.pair (codeo_const n) id_code)

-- -- helper lemma to prove rfind' case of univ theorem, since rfind' is defined differently from rfind
theorem rfind'o {g : ℕ →. ℕ} {cf : codeo}
    (hf : RecursiveIn g (evalo g cf)) :
  RecursiveIn g
    (Nat.unpaired fun a m =>
      (Nat.rfind fun n =>
        (fun m => m = 0) <$> evalo g cf (Nat.pair a (n + m))
      ).map (· + m))
 := sorry

/-- A function is partial recursive relative to an indexed set of oracles `O` if and only if there is a code implementing it.
Therefore, `evalo` is a **universal partial recursive function relative to `g`**. -/
theorem exists_code_rel (O : ℕ →. ℕ) (f : ℕ →. ℕ) :
  RecursiveIn O f ↔ ∃ c : codeo, evalo O c = f := by
  constructor
  · intro gf
    induction gf
    · exact ⟨codeo.zero, rfl⟩
    · exact ⟨codeo.succ, rfl⟩
    · exact ⟨codeo.left, rfl⟩
    · exact ⟨codeo.right, rfl⟩
    · sorry
    -- · case mp.oracle hf =>
    --   rcases hf with ⟨cf, rfl⟩
    --   exact ⟨codeo.oracle (encode cf), by
    --     funext n
    --     simp only [evalo, codeo.oracle]
    --     rw [encodek]⟩
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
    | oracle =>
      exact RecursiveIn.oracle
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


-- open Nat.Partrec.Code in
-- theorem Primrec.codeo_const {O : ℕ →. ℕ} : Primrec const := by
theorem Primrec.codeo_const {O : ℕ →. ℕ} : Primrec (fun n => encodeCodeo $ codeo_const n) := by
  sorry
  -- apply (_root_.Primrec.id.nat_iterate (_root_.Primrec.const Nat.Partrec.Code.zero) (primrec₂_comp.comp (_root_.Primrec.const succ) Primrec.snd).to₂)
  -- (_root_.Primrec.id.nat_iterate (_root_.Primrec.const zero)
  --   (primrec₂_comp.comp (_root_.Primrec.const succ) Primrec.snd).to₂).of_eq
  --   fun n => by simp; induction n <;>
  --     simp [*, Code.const, Function.iterate_succ', -Function.iterate_succ]
theorem RecursiveIn.codeo_const {O : ℕ →. ℕ} : RecursiveIn O (fun n => encodeCodeo $ codeo_const n) := by sorry

theorem exists_codeN_rel (O : ℕ →. ℕ) (f : ℕ →. ℕ) :
  RecursiveIn O f ↔ ∃ c : ℕ , evalo O c = f := by sorry


theorem RecursiveIn.evalo_computable {O:ℕ→.ℕ}: RecursiveIn O (fun x => evalo O (x.unpair.1) x.unpair.2) := by sorry


/--
codeo_calculate takes as input a pair (e,x), and returns an index to a program which
calculates ψᴼₑ(x) regardless of its input.
-/
def codeo_calculate := (fun ex => 1 : ℕ→ℕ) -- placeholder
theorem codeo_calculate' : evalo O (codeo_calculate (Nat.pair e x)) _z = evalo O e x := by sorry

theorem Primrec.codeo_calculate : Nat.Primrec (fun ex => codeo_calculate ex) := by
  sorry
