import Mathlib.Computability.Primrec


open List (Vector)
open Denumerable Encodable Function

namespace Nat

-- /-- Calls the given function on a pair of entries `n`, encoded via the pairing function. -/
-- @[simp, reducible]
-- def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
--   f n.unpair.1 n.unpair.2

/-- The primitive recursive functions `ℕ → ℕ`. -/
protected inductive PrimrecIn (O:ℕ→ℕ) : (ℕ → ℕ) → Prop
  | zero : Nat.PrimrecIn O fun _ => 0
  | protected succ : Nat.PrimrecIn O succ
  | left : Nat.PrimrecIn O fun n => n.unpair.1
  | right : Nat.PrimrecIn O fun n => n.unpair.2
  | oracle : Nat.PrimrecIn O O
  | pair {f g} : Nat.PrimrecIn O f → Nat.PrimrecIn O g → Nat.PrimrecIn O fun n => pair (f n) (g n)
  | comp {f g} : Nat.PrimrecIn O f → Nat.PrimrecIn O g → Nat.PrimrecIn O fun n => f (g n)
  | prec {f g} :
      Nat.PrimrecIn O f →
        Nat.PrimrecIn O g →
          Nat.PrimrecIn O (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

theorem Primrec.to_PrimrecIn (hf : Nat.Primrec f) : Nat.PrimrecIn O f := by
  induction' hf
  · exact PrimrecIn.zero
  · exact PrimrecIn.succ
  · exact PrimrecIn.left
  · exact PrimrecIn.right
  · (expose_names; exact PrimrecIn.pair a_ih a_ih_1)
  · (expose_names; exact PrimrecIn.comp a_ih a_ih_1)
  · (expose_names; exact PrimrecIn.prec a_ih a_ih_1)


namespace PrimrecIn

theorem of_eq {f g : ℕ → ℕ} (hf : Nat.PrimrecIn O f) (H : ∀ n, f n = g n) : Nat.PrimrecIn O g :=
  (funext H : f = g) ▸ hf

theorem const : ∀ n : ℕ, Nat.PrimrecIn O fun _ => n
  | 0 => zero
  | n + 1 => PrimrecIn.succ.comp (const n)

protected theorem id : Nat.PrimrecIn O id :=
  (left.pair right).of_eq fun n => by simp

theorem prec1 {f} (m : ℕ) (hf : Nat.PrimrecIn O f) :
    Nat.PrimrecIn O fun n => n.rec m fun y IH => f <| Nat.pair y IH :=
  ((prec (const m) (hf.comp right)).comp (zero.pair PrimrecIn.id)).of_eq fun n => by simp

theorem casesOn1 {f} (m : ℕ) (hf : Nat.PrimrecIn O f) : Nat.PrimrecIn O (Nat.casesOn · m f) :=
  (prec1 m (hf.comp left)).of_eq <| by simp

-- Porting note: `Nat.PrimrecIn.casesOn` is already declared as a recursor.
theorem casesOn' {f g} (hf : Nat.PrimrecIn O f) (hg : Nat.PrimrecIn O g) :
    Nat.PrimrecIn O (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair z y) :=
  (prec hf (hg.comp (pair left (left.comp right)))).of_eq fun n => by simp

protected theorem swap : Nat.PrimrecIn O (unpaired (swap Nat.pair)) :=
  (pair right left).of_eq fun n => by simp

theorem swap' {f} (hf : Nat.PrimrecIn O (unpaired f)) : Nat.PrimrecIn O (unpaired (swap f)) :=
  (hf.comp .swap).of_eq fun n => by simp

theorem pred : Nat.PrimrecIn O pred :=
  (casesOn1 0 PrimrecIn.id).of_eq fun n => by cases n <;> simp [*]

theorem add : Nat.PrimrecIn O (unpaired (· + ·)) :=
  (prec .id ((PrimrecIn.succ.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.add_assoc]

theorem sub : Nat.PrimrecIn O (unpaired (· - ·)) :=
  (prec .id ((pred.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.sub_add_eq]

theorem mul : Nat.PrimrecIn O (unpaired (· * ·)) :=
  (prec zero (add.comp (pair left (right.comp right)))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, mul_succ, add_comm _ (unpair p).fst]

theorem pow : Nat.PrimrecIn O (unpaired (· ^ ·)) :=
  (prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.pow_succ]

end PrimrecIn

end Nat

-- /-- A `Primcodable` type is an `Encodable` type for which
--   the encode/decode functions are primitive recursive. -/
-- class Primcodable (α : Type*) extends Encodable α where
--   -- Porting note: was `prim [] `.
--   -- This means that `prim` does not take the type explicitly in Lean 4
--   prim : Nat.PrimrecIn O fun n => Encodable.encode (decode n)

-- namespace Primcodable

-- open Nat.PrimrecIn O

-- instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α :=
--   ⟨Nat.PrimrecIn.succ.of_eq <| by simp⟩

-- /-- Builds a `Primcodable` instance from an equivalence to a `Primcodable` type. -/
-- def ofEquiv (α) {β} [Primcodable α] (e : β ≃ α) : Primcodable β :=
--   { __ := Encodable.ofEquiv α e
--     prim := (@Primcodable.prim α _).of_eq fun n => by
--       rw [decode_ofEquiv]
--       cases (@decode α _ n) <;>
--         simp [encode_ofEquiv] }

-- instance empty : Primcodable Empty :=
--   ⟨zero⟩

-- instance unit : Primcodable PUnit :=
--   ⟨(casesOn1 1 zero).of_eq fun n => by cases n <;> simp⟩

-- instance option {α : Type*} [h : Primcodable α] : Primcodable (Option α) :=
--   ⟨(casesOn1 1 ((casesOn1 0 (.comp .succ .succ)).comp (@Primcodable.prim α _))).of_eq fun n => by
--     cases n with
--       | zero => rfl
--       | succ n =>
--         rw [decode_option_succ]
--         cases H : @decode α _ n <;> simp [H]⟩

-- instance bool : Primcodable Bool :=
--   ⟨(casesOn1 1 (casesOn1 2 zero)).of_eq fun n => match n with
--     | 0 => rfl
--     | 1 => rfl
--     | (n + 2) => by rw [decode_ge_two] <;> simp⟩

-- end Primcodable

/-- `PrimrecIn O f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers). -/
def PrimrecIn (O:ℕ→ℕ) {α β} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Nat.PrimrecIn O fun n => encode ((@decode α _ n).map f)

theorem Primrec.to_PrimrecIn {O} {α β} [Primcodable α] [Primcodable β] (f : α → β) (hf : Primrec f) : PrimrecIn O f := by exact Nat.Primrec.to_PrimrecIn hf


namespace PrimrecIn

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.PrimrecIn

protected theorem encode : PrimrecIn O (@encode α _) := Nat.Primrec.to_PrimrecIn Primrec.encode
protected theorem decode : PrimrecIn O (@decode α _) := Nat.Primrec.to_PrimrecIn Primrec.decode

theorem dom_denumerable {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    PrimrecIn O f ↔ Nat.PrimrecIn O fun n => encode (f (ofNat α n)) :=
  ⟨fun h => (pred.comp h).of_eq fun n => by simp, fun h =>
    (Nat.PrimrecIn.succ.comp h).of_eq fun n => by simp⟩

theorem nat_iff {f : ℕ → ℕ} : PrimrecIn O f ↔ Nat.PrimrecIn O f := dom_denumerable
theorem encdec : PrimrecIn O fun n => encode (@decode α _ n) := Nat.Primrec.to_PrimrecIn Primrec.encdec
theorem option_some : PrimrecIn O (@some α) := Nat.Primrec.to_PrimrecIn Primrec.option_some
theorem of_eq {f g : α → σ} (hf : PrimrecIn O f) (H : ∀ n, f n = g n) : PrimrecIn O g := (funext H : f = g) ▸ hf
theorem const (x : σ) : PrimrecIn O fun _ : α => x := Nat.Primrec.to_PrimrecIn (Primrec.const x)
protected theorem id : PrimrecIn O (@id α) := Nat.Primrec.to_PrimrecIn Primrec.id

theorem comp {f : β → σ} {g : α → β} (hf : PrimrecIn O f) (hg : PrimrecIn O g) : PrimrecIn O fun a => f (g a) :=
  ((casesOn1 0 (.comp hf (pred.comp hg))).comp (Nat.Primrec.to_PrimrecIn (@Primcodable.prim α _))).of_eq fun n => by
    cases @decode α _ n <;> simp [encodek]

theorem succ : PrimrecIn O Nat.succ :=
  nat_iff.2 Nat.PrimrecIn.succ

theorem oracle : PrimrecIn O O := nat_iff.2 Nat.PrimrecIn.oracle

theorem pred : PrimrecIn O Nat.pred :=
  nat_iff.2 Nat.PrimrecIn.pred

theorem encode_iff {f : α → σ} : (PrimrecIn O fun a => encode (f a)) ↔ PrimrecIn O f :=
  ⟨fun h => Nat.PrimrecIn.of_eq h fun n => by cases @decode α _ n <;> rfl, PrimrecIn.encode.comp⟩

theorem ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    PrimrecIn O f ↔ PrimrecIn O fun n => f (ofNat α n) :=
  dom_denumerable.trans <| nat_iff.symm.trans encode_iff

protected theorem ofNat (α) [Denumerable α] : PrimrecIn O (ofNat α) :=
  ofNat_iff.1 PrimrecIn.id

theorem option_some_iff {f : α → σ} : (PrimrecIn O fun a => some (f a)) ↔ PrimrecIn O f :=
  ⟨fun h => encode_iff.1 <| pred.comp <| encode_iff.2 h, option_some.comp⟩

theorem of_equiv {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    PrimrecIn O e :=
  letI : Primcodable β := Primcodable.ofEquiv α e
  encode_iff.1 PrimrecIn.encode

theorem of_equiv_symm {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    PrimrecIn O e.symm :=
  letI := Primcodable.ofEquiv α e
  encode_iff.1 (show PrimrecIn O fun a => encode (e (e.symm a)) by simp [PrimrecIn.encode])

theorem of_equiv_iff {β} (e : β ≃ α) {f : σ → β} :
    haveI := Primcodable.ofEquiv α e
    (PrimrecIn O fun a => e (f a)) ↔ PrimrecIn O f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv_symm.comp h).of_eq fun a => by simp, of_equiv.comp⟩

theorem of_equiv_symm_iff {β} (e : β ≃ α) {f : σ → α} :
    haveI := Primcodable.ofEquiv α e
    (PrimrecIn O fun a => e.symm (f a)) ↔ PrimrecIn O f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv.comp h).of_eq fun a => by simp, of_equiv_symm.comp⟩

end PrimrecIn

namespace Primcodable

open Nat.PrimrecIn

-- instance prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β) :=
--   ⟨((casesOn' zero ((casesOn' zero .succ).comp (pair right ((@Primcodable.prim β).comp left)))).comp
--           (pair right ((@Primcodable.prim α).comp left))).of_eq
--       fun n => by
--       simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
--       cases @decode α _ n.unpair.1; · simp
--       cases @decode β _ n.unpair.2 <;> simp⟩

end Primcodable

namespace PrimrecIn

variable {α : Type*} [Primcodable α]

open Nat.PrimrecIn

theorem fst {α β} [Primcodable α] [Primcodable β] : PrimrecIn O (@Prod.fst α β) :=
  ((casesOn' zero
            ((casesOn' zero (Nat.PrimrecIn.succ.comp left)).comp
              (pair right ((Nat.Primrec.to_PrimrecIn (@Primcodable.prim β _)).comp left)))).comp
        (pair right ((Nat.Primrec.to_PrimrecIn (@Primcodable.prim α _)).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

theorem snd {α β} [Primcodable α] [Primcodable β] : PrimrecIn O (@Prod.snd α β) :=
  ((casesOn' zero
            ((casesOn' zero (Nat.PrimrecIn.succ.comp right)).comp
              (pair right ((Nat.Primrec.to_PrimrecIn (@Primcodable.prim β _)).comp left)))).comp
        (pair right ((Nat.Primrec.to_PrimrecIn (@Primcodable.prim α _)).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

theorem pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : PrimrecIn O f) (hg : PrimrecIn O g) : PrimrecIn O fun a => (f a, g a) :=
  ((casesOn1 0
            (Nat.PrimrecIn.succ.comp <|
              .pair (Nat.PrimrecIn.pred.comp hf) (Nat.PrimrecIn.pred.comp hg))).comp
        (Nat.Primrec.to_PrimrecIn (@Primcodable.prim α _))).of_eq
    fun n => by cases @decode α _ n <;> simp [encodek]

theorem unpair : PrimrecIn O Nat.unpair :=
  (pair (nat_iff.2 .left) (nat_iff.2 .right)).of_eq fun n => by simp

theorem list_get?₁ : ∀ l : List α, PrimrecIn O l.get?
  | [] => dom_denumerable.2 zero
  | a :: l =>
    dom_denumerable.2 <|
      (casesOn1 (encode a).succ <| dom_denumerable.1 <| list_get?₁ l).of_eq fun n => by
        cases n <;> simp

end PrimrecIn

/-- `PrimrecIn₂ O f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly. -/
def PrimrecIn₂ (O) {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  PrimrecIn O fun p : α × β => f p.1 p.2

/-- `PrimrecInPred O p` means `p : α → Prop` is a (decidable)
  primitive recursive predicate, which is to say that
  `decide ∘ p : α → Bool` is primitive recursive. -/
def PrimrecInPred (O) {α} [Primcodable α] (p : α → Prop) [DecidablePred p] :=
  PrimrecIn O fun a => decide (p a)

/-- `PrimrecInRel O p` means `p : α → β → Prop` is a (decidable)
  primitive recursive relation, which is to say that
  `decide ∘ p : α → β → Bool` is primitive recursive. -/
def PrimrecInRel (O) {α β} [Primcodable α] [Primcodable β] (s : α → β → Prop)
    [∀ a b, Decidable (s a b)] :=
  PrimrecIn₂ O fun a b => decide (s a b)

namespace PrimrecIn₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

theorem mk {f : α → β → σ} (hf : PrimrecIn O fun p : α × β => f p.1 p.2) : PrimrecIn₂ O f := hf

theorem of_eq {f g : α → β → σ} (hg : PrimrecIn₂ O f) (H : ∀ a b, f a b = g a b) : PrimrecIn₂ O g :=
  (by funext a b; apply H : f = g) ▸ hg

theorem const (x : σ) : PrimrecIn₂ O fun (_ : α) (_ : β) => x :=
  PrimrecIn.const _

protected theorem pair : PrimrecIn₂ O (@Prod.mk α β) :=
  PrimrecIn.pair .fst .snd

theorem left : PrimrecIn₂ O fun (a : α) (_ : β) => a :=
  .fst

theorem right : PrimrecIn₂ O fun (_ : α) (b : β) => b :=
  .snd

theorem natPair : PrimrecIn₂ O Nat.pair := by simp [PrimrecIn₂, PrimrecIn]; constructor

theorem unpaired {f : ℕ → ℕ → α} : PrimrecIn O (Nat.unpaired f) ↔ PrimrecIn₂ O f :=
  ⟨fun h => by simpa using h.comp natPair, fun h => h.comp PrimrecIn.unpair⟩

theorem unpaired' {f : ℕ → ℕ → ℕ} : Nat.PrimrecIn O (Nat.unpaired f) ↔ PrimrecIn₂ O f :=
  PrimrecIn.nat_iff.symm.trans unpaired

theorem encode_iff {f : α → β → σ} : (PrimrecIn₂ O fun a b => encode (f a b)) ↔ PrimrecIn₂ O f :=
  PrimrecIn.encode_iff

theorem option_some_iff {f : α → β → σ} : (PrimrecIn₂ O fun a b => some (f a b)) ↔ PrimrecIn₂ O f :=
  PrimrecIn.option_some_iff

theorem ofNat_iff {α β σ} [Denumerable α] [Denumerable β] [Primcodable σ] {f : α → β → σ} :
    PrimrecIn₂ O f ↔ PrimrecIn₂ O fun m n : ℕ => f (ofNat α m) (ofNat β n) :=
  (PrimrecIn.ofNat_iff.trans <| by simp).trans unpaired

theorem uncurry {f : α → β → σ} : PrimrecIn O (Function.uncurry f) ↔ PrimrecIn₂ O f := by
  rw [show Function.uncurry f = fun p : α × β => f p.1 p.2 from funext fun ⟨a, b⟩ => rfl]; rfl

theorem curry {f : α × β → σ} : PrimrecIn₂ O (Function.curry f) ↔ PrimrecIn O f := by
  rw [← uncurry, Function.uncurry_curry]

end PrimrecIn₂

section Comp

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

theorem PrimrecIn.comp₂ {f : γ → σ} {g : α → β → γ} (hf : PrimrecIn O f) (hg : PrimrecIn₂ O g) :
    PrimrecIn₂ O fun a b => f (g a b) :=
  hf.comp hg

theorem PrimrecIn₂.comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : PrimrecIn₂ O f) (hg : PrimrecIn O g)
    (hh : PrimrecIn O h) : PrimrecIn O fun a => f (g a) (h a) :=
  PrimrecIn.comp hf (hg.pair hh)

theorem PrimrecIn₂.comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : PrimrecIn₂ O f)
    (hg : PrimrecIn₂ O g) (hh : PrimrecIn₂ O h) : PrimrecIn₂ O fun a b => f (g a b) (h a b) :=
  hf.comp hg hh

theorem PrimrecInPred.comp {p : β → Prop} [DecidablePred p] {f : α → β} :
    PrimrecInPred O p → PrimrecIn O f → PrimrecInPred O fun a => p (f a) :=
  PrimrecIn.comp

theorem PrimrecInRel.comp {R : β → γ → Prop} [∀ a b, Decidable (R a b)] {f : α → β} {g : α → γ} :
    PrimrecInRel O R → PrimrecIn O f → PrimrecIn O g → PrimrecInPred O fun a => R (f a) (g a) :=
  PrimrecIn₂.comp

theorem PrimrecInRel.comp₂ {R : γ → δ → Prop} [∀ a b, Decidable (R a b)] {f : α → β → γ}
    {g : α → β → δ} :
    PrimrecInRel O R → PrimrecIn₂ O f → PrimrecIn₂ O g → PrimrecInRel O fun a b => R (f a b) (g a b) :=
  PrimrecInRel.comp

end Comp

theorem PrimrecInPred.of_eq {α} [Primcodable α] {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecInPred O p) (H : ∀ a, p a ↔ q a) : PrimrecInPred O q :=
  PrimrecIn.of_eq hp fun a => Bool.decide_congr (H a)

theorem PrimrecInRel.of_eq {α β} [Primcodable α] [Primcodable β] {r s : α → β → Prop}
    [∀ a b, Decidable (r a b)] [∀ a b, Decidable (s a b)] (hr : PrimrecInRel O r)
    (H : ∀ a b, r a b ↔ s a b) : PrimrecInRel O s :=
  PrimrecIn₂.of_eq hr fun a b => Bool.decide_congr (H a b)

namespace PrimrecIn₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.PrimrecIn

theorem swap {f : α → β → σ} (h : PrimrecIn₂ O f) : PrimrecIn₂ O (swap f) :=
  h.comp₂ PrimrecIn₂.right PrimrecIn₂.left

theorem nat_iff {f : α → β → σ} : PrimrecIn₂ O f ↔ Nat.PrimrecIn O
    (.unpaired fun m n => encode <| (@decode α _ m).bind fun a => (@decode β _ n).map (f a)) := by
  have :
    ∀ (a : Option α) (b : Option β),
      Option.map (fun p : α × β => f p.1 p.2)
          (Option.bind a fun a : α => Option.map (Prod.mk a) b) =
        Option.bind a fun a => Option.map (f a) b := fun a b => by
          cases a <;> cases b <;> rfl
  simp [PrimrecIn₂, PrimrecIn, this]

theorem nat_iff' {f : α → β → σ} :
    PrimrecIn₂ O f ↔
      PrimrecIn₂ O fun m n : ℕ => (@decode α _ m).bind fun a => Option.map (f a) (@decode β _ n) :=
  nat_iff.trans <| unpaired'.trans encode_iff

end PrimrecIn₂

namespace PrimrecIn

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

theorem to₂ {f : α × β → σ} (hf : PrimrecIn O f) : PrimrecIn₂ O fun a b => f (a, b) :=
  hf.of_eq fun _ => rfl

theorem nat_rec {f : α → β} {g : α → ℕ × β → β} (hf : PrimrecIn O f) (hg : PrimrecIn₂ O g) :
    PrimrecIn₂ O fun a (n : ℕ) => n.rec (motive := fun _ => β) (f a) fun n IH => g a (n, IH) :=
  PrimrecIn₂.nat_iff.2 <|
    ((Nat.PrimrecIn.casesOn' .zero <|
              (Nat.PrimrecIn.prec hf <|
                    .comp hg <|
                      Nat.PrimrecIn.left.pair <|
                        (Nat.PrimrecIn.left.comp .right).pair <|
                          Nat.PrimrecIn.pred.comp <| Nat.PrimrecIn.right.comp .right).comp <|
                Nat.PrimrecIn.right.pair <| Nat.PrimrecIn.right.comp Nat.PrimrecIn.left).comp <|
          Nat.PrimrecIn.id.pair <| (Nat.Primrec.to_PrimrecIn (@Primcodable.prim α _)).comp Nat.PrimrecIn.left).of_eq
      fun n => by
      simp only [Nat.unpaired, id_eq, Nat.unpair_pair, decode_prod_val, decode_nat,
        Option.bind_some, Option.map_map, Option.map_some]
      rcases @decode α _ n.unpair.1 with - | a; · rfl
      simp only [Nat.pred_eq_sub_one, encode_some, Nat.succ_eq_add_one, encodek, Option.map_some,
        Option.bind_some, Option.map_map]
      induction' n.unpair.2 with m <;> simp
      simp [*, encodek]

theorem nat_rec' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β}
    (hf : PrimrecIn O f) (hg : PrimrecIn O g) (hh : PrimrecIn₂ O h) :
    PrimrecIn O fun a => (f a).rec (motive := fun _ => β) (g a) fun n IH => h a (n, IH) :=
  (nat_rec hg hh).comp .id hf

theorem nat_rec₁ {f : ℕ → α → α} (a : α) (hf : PrimrecIn₂ O f) : PrimrecIn O (Nat.rec a f) :=
  nat_rec' .id (const a) <| comp₂ hf PrimrecIn₂.right

theorem nat_casesOn' {f : α → β} {g : α → ℕ → β} (hf : PrimrecIn O f) (hg : PrimrecIn₂ O g) :
    PrimrecIn₂ O fun a (n : ℕ) => (n.casesOn (f a) (g a) : β) :=
  nat_rec hf <| hg.comp₂ PrimrecIn₂.left <| comp₂ fst PrimrecIn₂.right

theorem nat_casesOn {f : α → ℕ} {g : α → β} {h : α → ℕ → β} (hf : PrimrecIn O f) (hg : PrimrecIn O g)
    (hh : PrimrecIn₂ O h) : PrimrecIn O fun a => ((f a).casesOn (g a) (h a) : β) :=
  (nat_casesOn' hg hh).comp .id hf

theorem nat_casesOn₁ {f : ℕ → α} (a : α) (hf : PrimrecIn O f) :
    PrimrecIn O (fun (n : ℕ) => (n.casesOn a f : α)) :=
  nat_casesOn .id (const a) (comp₂ hf .right)

theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β} (hf : PrimrecIn O f) (hg : PrimrecIn O g)
    (hh : PrimrecIn₂ O h) : PrimrecIn O fun a => (h a)^[f a] (g a) :=
  (nat_rec' hf hg (hh.comp₂ PrimrecIn₂.left <| snd.comp₂ PrimrecIn₂.right)).of_eq fun a => by
    induction f a <;> simp [*, -Function.iterate_succ, Function.iterate_succ']

theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : PrimrecIn O o)
    (hf : PrimrecIn O f) (hg : PrimrecIn₂ O g) :
    @PrimrecIn O _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  encode_iff.1 <|
    (nat_casesOn (encode_iff.2 ho) (encode_iff.2 hf) <|
          pred.comp₂ <|
            PrimrecIn₂.encode_iff.2 <|
              (PrimrecIn₂.nat_iff'.1 hg).comp₂ ((@PrimrecIn.encode α _).comp fst).to₂
                PrimrecIn₂.right).of_eq
      fun a => by rcases o a with - | b <;> simp [encodek]

theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : PrimrecIn O f) (hg : PrimrecIn₂ O g) :
    PrimrecIn O fun a => (f a).bind (g a) :=
  (option_casesOn hf (const none) hg).of_eq fun a => by cases f a <;> rfl

theorem option_bind₁ {f : α → Option σ} (hf : PrimrecIn O f) : PrimrecIn O fun o => Option.bind o f :=
  option_bind .id (hf.comp snd).to₂

theorem option_map {f : α → Option β} {g : α → β → σ} (hf : PrimrecIn O f) (hg : PrimrecIn₂ O g) :
    PrimrecIn O fun a => (f a).map (g a) :=
  (option_bind hf (option_some.comp₂ hg)).of_eq fun x => by cases f x <;> rfl

theorem option_map₁ {f : α → σ} (hf : PrimrecIn O f) : PrimrecIn O (Option.map f) :=
  option_map .id (hf.comp snd).to₂

theorem option_iget [Inhabited α] : PrimrecIn O (@Option.iget α _) :=
  (option_casesOn .id (const <| @default α _) .right).of_eq fun o => by cases o <;> rfl

theorem option_isSome : PrimrecIn O (@Option.isSome α) :=
  (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl

theorem option_getD : PrimrecIn₂ O (@Option.getD α) :=
  PrimrecIn.of_eq (option_casesOn PrimrecIn₂.left PrimrecIn₂.right .right) fun ⟨o, a⟩ => by
    cases o <;> rfl

theorem bind_decode_iff {f : α → β → Option σ} :
    (PrimrecIn₂ O fun a n => (@decode β _ n).bind (f a)) ↔ PrimrecIn₂ O f :=
  ⟨fun h => by simpa [encodek] using h.comp fst ((@PrimrecIn.encode β _).comp snd), fun h =>
    option_bind (PrimrecIn.decode.comp snd) <| h.comp (fst.comp fst) snd⟩

theorem map_decode_iff {f : α → β → σ} :
    (PrimrecIn₂ O fun a n => (@decode β _ n).map (f a)) ↔ PrimrecIn₂ O f := by
  simp only [Option.map_eq_bind]
  exact bind_decode_iff.trans PrimrecIn₂.option_some_iff

theorem nat_add : PrimrecIn₂ O ((· + ·) : ℕ → ℕ → ℕ) :=
  PrimrecIn₂.unpaired'.1 Nat.PrimrecIn.add

theorem nat_sub : PrimrecIn₂ O ((· - ·) : ℕ → ℕ → ℕ) :=
  PrimrecIn₂.unpaired'.1 Nat.PrimrecIn.sub

theorem nat_mul : PrimrecIn₂ O ((· * ·) : ℕ → ℕ → ℕ) :=
  PrimrecIn₂.unpaired'.1 Nat.PrimrecIn.mul

theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : PrimrecIn O c) (hf : PrimrecIn O f)
    (hg : PrimrecIn O g) : PrimrecIn O fun a => bif (c a) then (f a) else (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

theorem ite {c : α → Prop} [DecidablePred c] {f : α → σ} {g : α → σ} (hc : PrimrecInPred O c)
    (hf : PrimrecIn O f) (hg : PrimrecIn O g) : PrimrecIn O fun a => if c a then f a else g a := by
  simpa [Bool.cond_decide] using cond hc hf hg

theorem nat_le : PrimrecInRel O ((· ≤ ·) : ℕ → ℕ → Prop) :=
  (nat_casesOn nat_sub (const true) (const false).to₂).of_eq fun p => by
    dsimp [swap]
    rcases e : p.1 - p.2 with - | n
    · simp [Nat.sub_eq_zero_iff_le.1 e]
    · simp [not_le.2 (Nat.lt_of_sub_eq_succ e)]

theorem nat_min : PrimrecIn₂ O (@min ℕ _) :=
  ite nat_le fst snd

theorem nat_max : PrimrecIn₂ O (@max ℕ _) :=
  ite (nat_le.comp fst snd) snd fst

theorem dom_bool (f : Bool → α) : PrimrecIn O f :=
  (cond .id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl

theorem dom_bool₂ (f : Bool → Bool → α) : PrimrecIn₂ O f :=
  (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl

protected theorem not : PrimrecIn O not :=
  dom_bool _

protected theorem and : PrimrecIn₂ O and :=
  dom_bool₂ _

protected theorem or : PrimrecIn₂ O or :=
  dom_bool₂ _

theorem _root_.PrimrecInPred.not {p : α → Prop} [DecidablePred p] (hp : PrimrecInPred O p) :
    PrimrecInPred O fun a => ¬p a :=
  (PrimrecIn.not.comp hp).of_eq fun n => by simp

theorem _root_.PrimrecInPred.and {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecInPred O p) (hq : PrimrecInPred O q) : PrimrecInPred O fun a => p a ∧ q a :=
  (PrimrecIn.and.comp hp hq).of_eq fun n => by simp

theorem _root_.PrimrecInPred.or {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : PrimrecInPred O p) (hq : PrimrecInPred O q) : PrimrecInPred O fun a => p a ∨ q a :=
  (PrimrecIn.or.comp hp hq).of_eq fun n => by simp

protected theorem beq [DecidableEq α] : PrimrecIn₂ O (@BEq.beq α _) :=
  have : PrimrecInRel O fun a b : ℕ => a = b :=
    (PrimrecInPred.and nat_le nat_le.swap).of_eq fun a => by simp [le_antisymm_iff]
  (this.comp₂ (PrimrecIn.encode.comp₂ PrimrecIn₂.left) (PrimrecIn.encode.comp₂ PrimrecIn₂.right)).of_eq
    fun _ _ => encode_injective.eq_iff

protected theorem eq [DecidableEq α] : PrimrecInRel O (@Eq α) := PrimrecIn.beq

theorem nat_lt : PrimrecInRel O ((· < ·) : ℕ → ℕ → Prop) :=
  -- (nat_le.comp snd fst).not.of_eq fun p => by simp
  (PrimrecInPred.not (nat_le.comp snd fst)).of_eq fun p => by simp

theorem option_guard {p : α → β → Prop} [∀ a b, Decidable (p a b)] (hp : PrimrecInRel O p) {f : α → β}
    (hf : PrimrecIn O f) : PrimrecIn O fun a => Option.guard (p a) (f a) :=
  -- ite (hp.comp PrimrecIn.id hf) (option_some_iff.2 hf) (const none)
  ite (by
    refine PrimrecInRel.comp ?_ ?_ ?_
    exact PrimrecIn.eq
    simp [*] at *
    · refine ite ?_ ?_ ?_
      · refine PrimrecInRel.comp hp ?_ hf
        exact PrimrecIn.id
      · exact const true
      · exact const false
    exact const true
    ) (option_some_iff.2 hf) (const none)
  -- ite (PrimrecInRel.comp hp PrimrecIn.id hf) (option_some_iff.2 hf) (const none)

theorem option_orElse : PrimrecIn₂ O ((· <|> ·) : Option α → Option α → Option α) :=
  (option_casesOn fst snd (fst.comp fst).to₂).of_eq fun ⟨o₁, o₂⟩ => by cases o₁ <;> cases o₂ <;> rfl

protected theorem decode₂ : PrimrecIn O (decode₂ α) :=
  option_bind .decode <|
    option_guard (PrimrecIn.beq.comp₂ (by exact encode_iff.mpr snd) (by exact fst.comp fst)) snd

theorem list_findIdx₁ {p : α → β → Bool} (hp : PrimrecIn₂ O p) :
    ∀ l : List β, PrimrecIn O fun a => l.findIdx (p a)
| [] => const 0
| a :: l => (cond (hp.comp .id (const a)) (const 0) (succ.comp (list_findIdx₁ hp l))).of_eq fun n =>
  by simp [List.findIdx_cons]

theorem list_idxOf₁ [DecidableEq α] (l : List α) : PrimrecIn O fun a => l.idxOf a :=
  list_findIdx₁ (.swap .beq) l

@[deprecated (since := "2025-01-30")] alias list_indexOf₁ := list_idxOf₁

theorem dom_fintype [Finite α] (f : α → σ) : PrimrecIn O f :=
  let ⟨l, _, m⟩ := Finite.exists_univ_list α
  option_some_iff.1 <| by
    haveI := decidableEqOfEncodable α
    refine ((list_get?₁ (l.map f)).comp (list_idxOf₁ l)).of_eq fun a => ?_
    rw [List.get?_eq_getElem?, List.getElem?_map, List.getElem?_idxOf (m a), Option.map_some]

-- Porting note: These are new lemmas
-- I added it because it actually simplified the proofs
-- and because I couldn't understand the original proof
/-- A function is `PrimrecInBounded O` if its size is bounded by a primitive recursive function -/
def PrimrecInBounded (O:ℕ→ℕ) (f : α → β) : Prop :=
  ∃ g : α → ℕ, PrimrecIn O g ∧ ∀ x, encode (f x) ≤ g x

theorem nat_findGreatest {f : α → ℕ} {p : α → ℕ → Prop} [∀ x n, Decidable (p x n)]
    (hf : PrimrecIn O f) (hp : PrimrecInRel O p) : PrimrecIn O fun x => (f x).findGreatest (p x) :=
  (nat_rec' (h := fun x nih => if p x (nih.1 + 1) then nih.1 + 1 else nih.2)
    hf (const 0) (ite (hp.comp fst (snd |> fst.comp |> succ.comp))
      (snd |> fst.comp |> succ.comp) (snd.comp snd))).of_eq fun x => by
        induction f x <;> simp [Nat.findGreatest, *]

/-- To show a function `f : α → ℕ` is primitive recursive, it is enough to show that the function
  is bounded by a primitive recursive function and that its graph is primitive recursive -/
theorem of_graph {f : α → ℕ} (h₁ : PrimrecInBounded O f)
    (h₂ : PrimrecInRel O fun a b => f a = b) : PrimrecIn O f := by
  rcases h₁ with ⟨g, pg, hg : ∀ x, f x ≤ g x⟩
  refine (nat_findGreatest pg h₂).of_eq fun n => ?_
  exact (Nat.findGreatest_spec (P := fun b => f n = b) (hg n) rfl).symm

-- We show that division is primitive recursive by showing that the graph is
theorem nat_div : PrimrecIn₂ O ((· / ·) : ℕ → ℕ → ℕ) := by
  refine of_graph ⟨_, fst, fun p => Nat.div_le_self _ _⟩ ?_
  have : PrimrecInRel O fun (a : ℕ × ℕ) (b : ℕ) => (a.2 = 0 ∧ b = 0) ∨
      (0 < a.2 ∧ b * a.2 ≤ a.1 ∧ a.1 < (b + 1) * a.2) :=
    PrimrecInPred.or
      (.and (const 0 |> PrimrecIn.eq.comp (fst |> snd.comp)) (const 0 |> PrimrecIn.eq.comp snd))
      (.and (nat_lt.comp (const 0) (fst |> snd.comp)) <|
          .and (nat_le.comp (nat_mul.comp snd (fst |> snd.comp)) (fst |> fst.comp))
          (nat_lt.comp (fst.comp fst) (nat_mul.comp (PrimrecIn.succ.comp snd) (snd.comp fst))))
  refine this.of_eq ?_
  rintro ⟨a, k⟩ q
  if H : k = 0 then simp [H, eq_comm]
  else
    have : q * k ≤ a ∧ a < (q + 1) * k ↔ q = a / k := by
      rw [le_antisymm_iff, ← (@Nat.lt_succ _ q), Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero H),
          Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero H)]
    simpa [H, zero_lt_iff, eq_comm (b := q)]

theorem nat_mod : PrimrecIn₂ O ((· % ·) : ℕ → ℕ → ℕ) :=
  (nat_sub.comp fst (nat_mul.comp snd nat_div)).to₂.of_eq fun m n => by
    apply Nat.sub_eq_of_eq_add
    simp [add_comm (m % n), Nat.div_add_mod]

theorem nat_bodd : PrimrecIn O Nat.bodd :=
  (PrimrecIn.beq.comp (nat_mod.comp .id (const 2)) (const 1)).of_eq fun n => by
    cases H : n.bodd <;> simp [Nat.mod_two_of_bodd, H]

theorem nat_div2 : PrimrecIn O Nat.div2 :=
  (nat_div.comp .id (const 2)).of_eq fun n => n.div2_val.symm

theorem nat_double : PrimrecIn O (fun n : ℕ => 2 * n) :=
  nat_mul.comp (const _) PrimrecIn.id

theorem nat_double_succ : PrimrecIn O (fun n : ℕ => 2 * n + 1) :=
  nat_double |> PrimrecIn.succ.comp

end PrimrecIn

section

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]
variable (H : Nat.Primrec fun n => Encodable.encode (@decode (List β) _ n))

open PrimrecIn

private def prim : Primcodable (List β) := ⟨H⟩

private theorem list_casesOn' {f : α → List β} {g : α → σ} {h : α → β × List β → σ}
    (hf : haveI := prim H; PrimrecIn O f) (hg : PrimrecIn O g) (hh : haveI := prim H; PrimrecIn₂ O h) :
    @PrimrecIn O _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  letI := prim H
  have :
    @PrimrecIn O _ (Option σ) _ _ fun a =>
      (@decode (Option (β × List β)) _ (encode (f a))).map fun o => Option.casesOn o (g a) (h a) :=
    ((@map_decode_iff _ (Option (β × List β)) _ _ _ _ _).2 <|
      to₂ <|
        option_casesOn snd (hg.comp fst) (hh.comp₂ (fst.comp₂ PrimrecIn₂.left) PrimrecIn₂.right)).comp
      .id (encode_iff.2 hf)
  option_some_iff.1 <| this.of_eq fun a => by rcases f a with - | ⟨b, l⟩ <;> simp [encodek]

private theorem list_foldl' {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : haveI := prim H; PrimrecIn O f) (hg : PrimrecIn O g) (hh : haveI := prim H; PrimrecIn₂ O h) :
    PrimrecIn O fun a => (f a).foldl (fun s b => h a (s, b)) (g a) := by
  letI := prim H
  let G (a : α) (IH : σ × List β) : σ × List β := List.casesOn IH.2 IH fun b l => (h a (IH.1, b), l)
  have hG : PrimrecIn₂ O G := list_casesOn' H (snd.comp snd) snd <|
    to₂ <|
    pair (hh.comp (fst.comp fst) <| pair ((fst.comp snd).comp fst) (fst.comp snd))
      (snd.comp snd)
  let F := fun (a : α) (n : ℕ) => (G a)^[n] (g a, f a)
  have hF : PrimrecIn O fun a => (F a (encode (f a))).1 :=
    (fst.comp <|
      nat_iterate (encode_iff.2 hf) (pair hg hf) <|
      hG)
  suffices ∀ a n, F a n = (((f a).take n).foldl (fun s b => h a (s, b)) (g a), (f a).drop n) by
    refine hF.of_eq fun a => ?_
    rw [this, List.take_of_length_le (length_le_encode _)]
  introv
  dsimp only [F]
  generalize f a = l
  generalize g a = x
  induction n generalizing l x with
  | zero => rfl
  | succ n IH =>
    simp only [iterate_succ, comp_apply]
    rcases l with - | ⟨b, l⟩ <;> simp [G, IH]

private theorem list_cons' : (haveI := prim H; PrimrecIn₂ O (@List.cons β)) :=
  letI := prim H
  encode_iff.1 (succ.comp <| PrimrecIn₂.natPair.comp (encode_iff.2 fst) (encode_iff.2 snd))

private theorem list_reverse' :
    haveI := prim H
    PrimrecIn O (@List.reverse β) :=
  letI := prim H
  (list_foldl' H .id (const []) <| to₂ <| ((list_cons' H).comp snd fst).comp snd).of_eq
    (suffices ∀ l r, List.foldl (fun (s : List β) (b : β) => b :: s) r l = List.reverseAux l r from
      fun l => this l []
    fun l => by induction l <;> simp [*, List.reverseAux])

end

namespace Primcodable

variable {α : Type*} {β : Type*}
variable [Primcodable α] [Primcodable β]

open PrimrecIn

-- instance sum : Primcodable (α ⊕ β) :=
--   ⟨PrimrecIn.nat_iff.1 <|
--       (encode_iff.2
--             (cond nat_bodd
--               (((@PrimrecIn.decode β _).comp nat_div2).option_map <|
--                 to₂ <| nat_double_succ.comp (PrimrecIn.encode.comp snd))
--               (((@PrimrecIn.decode α _).comp nat_div2).option_map <|
--                 to₂ <| nat_double.comp (PrimrecIn.encode.comp snd)))).of_eq
--         fun n =>
--         show _ = encode (decodeSum n) by
--           simp only [decodeSum, Nat.boddDiv2_eq]
--           cases Nat.bodd n <;> simp [decodeSum]
--           · cases @decode α _ n.div2 <;> rfl
--           · cases @decode β _ n.div2 <;> rfl⟩

-- instance list : Primcodable (List α) :=
--   ⟨letI H := @Primcodable.prim (List ℕ) _
--     have : PrimrecIn₂ O fun (a : α) (o : Option (List ℕ)) => o.map (List.cons (encode a)) :=
--       option_map snd <| (list_cons' H).comp ((@PrimrecIn.encode α _).comp (fst.comp fst)) snd
--     have :
--       PrimrecIn O fun n =>
--         (ofNat (List ℕ) n).reverse.foldl
--           (fun o m => (@decode α _ m).bind fun a => o.map (List.cons (encode a))) (some []) :=
--       list_foldl' H ((list_reverse' H).comp (.ofNat (List ℕ))) (const (some []))
--         (PrimrecIn.comp₂ (bind_decode_iff.2 <| .swap this) PrimrecIn₂.right)
--     nat_iff.1 <|
--       (encode_iff.2 this).of_eq fun n => by
--         rw [List.foldl_reverse]
--         apply Nat.case_strong_induction_on n; · simp
--         intro n IH; simp
--         rcases @decode α _ n.unpair.1 with - | a; · rfl
--         simp only [decode_eq_ofNat, Option.some.injEq, Option.some_bind, Option.map_some']
--         suffices ∀ (o : Option (List ℕ)) (p), encode o = encode p →
--             encode (Option.map (List.cons (encode a)) o) = encode (Option.map (List.cons a) p) from
--           this _ _ (IH _ (Nat.unpair_right_le n))
--         intro o p IH
--         cases o <;> cases p
--         · rfl
--         · injection IH
--         · injection IH
--         · exact congr_arg (fun k => (Nat.pair (encode a) k).succ.succ) (Nat.succ.inj IH)⟩
end Primcodable

namespace PrimrecIn

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem sumInl : PrimrecIn O (@Sum.inl α β) :=
  encode_iff.1 <| nat_double.comp PrimrecIn.encode

theorem sumInr : PrimrecIn O (@Sum.inr α β) :=
  encode_iff.1 <| nat_double_succ.comp PrimrecIn.encode

@[deprecated (since := "2025-02-21")] alias sum_inl := PrimrecIn.sumInl
@[deprecated (since := "2025-02-21")] alias sum_inr := PrimrecIn.sumInr

theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ} (hf : PrimrecIn O f)
    (hg : PrimrecIn₂ O g) (hh : PrimrecIn₂ O h) : @PrimrecIn O _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (PrimrecIn.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (PrimrecIn.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by rcases f a with b | c <;> simp [Nat.div2_val, encodek]

@[deprecated (since := "2025-02-21")] alias sum_casesOn := PrimrecIn.sumCasesOn

theorem list_cons : PrimrecIn₂ O (@List.cons α) :=
  list_cons' Primcodable.prim

theorem list_casesOn {f : α → List β} {g : α → σ} {h : α → β × List β → σ} :
    PrimrecIn O f →
      PrimrecIn O g →
        PrimrecIn₂ O h → @PrimrecIn O _ σ _ _ fun a => List.casesOn (f a) (g a) fun b l => h a (b, l) :=
  list_casesOn' Primcodable.prim

theorem list_foldl {f : α → List β} {g : α → σ} {h : α → σ × β → σ} :
    PrimrecIn O f →
      PrimrecIn O g → PrimrecIn₂ O h → PrimrecIn O fun a => (f a).foldl (fun s b => h a (s, b)) (g a) :=
  list_foldl' Primcodable.prim

theorem list_reverse : PrimrecIn O (@List.reverse α) :=
  list_reverse' Primcodable.prim

theorem list_foldr {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (hf : PrimrecIn O f)
    (hg : PrimrecIn O g) (hh : PrimrecIn₂ O h) :
    PrimrecIn O fun a => (f a).foldr (fun b s => h a (b, s)) (g a) :=
  (list_foldl (list_reverse.comp hf) hg <| to₂ <| hh.comp fst <| (pair snd fst).comp snd).of_eq
    fun a => by simp [List.foldl_reverse]

theorem list_head? : PrimrecIn O (@List.head? α) :=
  (list_casesOn .id (const none) (option_some_iff.2 <| fst.comp snd).to₂).of_eq fun l => by
    cases l <;> rfl

theorem list_headI [Inhabited α] : PrimrecIn O (@List.headI α _) :=
  (option_iget.comp list_head?).of_eq fun l => l.head!_eq_head?.symm

theorem list_tail : PrimrecIn O (@List.tail α) :=
  (list_casesOn .id (const []) (snd.comp snd).to₂).of_eq fun l => by cases l <;> rfl

theorem list_rec {f : α → List β} {g : α → σ} {h : α → β × List β × σ → σ} (hf : PrimrecIn O f)
    (hg : PrimrecIn O g) (hh : PrimrecIn₂ O h) :
    @PrimrecIn O _ σ _ _ fun a => List.recOn (f a) (g a) fun b l IH => h a (b, l, IH) :=
  let F (a : α) := (f a).foldr (fun (b : β) (s : List β × σ) => (b :: s.1, h a (b, s))) ([], g a)
  have : PrimrecIn O F :=
    list_foldr hf (pair (const []) hg) <|
      to₂ <| pair ((list_cons.comp fst (fst.comp snd)).comp snd) hh
  (snd.comp this).of_eq fun a => by
    suffices F a = (f a, List.recOn (f a) (g a) fun b l IH => h a (b, l, IH)) by rw [this]
    dsimp [F]
    induction' f a with b l IH <;> simp [*]

theorem list_get? : PrimrecIn₂ O (@List.get? α) :=
  let F (l : List α) (n : ℕ) :=
    l.foldl
      (fun (s : ℕ ⊕ α) (a : α) =>
        Sum.casesOn s (@Nat.casesOn (fun _ => ℕ ⊕ α) · (Sum.inr a) Sum.inl) Sum.inr)
      (Sum.inl n)
  have hF : PrimrecIn₂ O F :=
    (list_foldl fst (sumInl.comp snd)
      ((sumCasesOn fst (nat_casesOn snd (sumInr.comp <| snd.comp fst) (sumInl.comp snd).to₂).to₂
              (sumInr.comp snd).to₂).comp
          snd).to₂).to₂
  have :
    @PrimrecIn O _ (Option α) _ _ fun p : List α × ℕ => Sum.casesOn (F p.1 p.2) (fun _ => none) some :=
    sumCasesOn hF (const none).to₂ (option_some.comp snd).to₂
  this.to₂.of_eq fun l n => by
    dsimp; symm
    induction' l with a l IH generalizing n; · rfl
    rcases n with - | n
    · dsimp [F]
      clear IH
      induction' l with _ l IH <;> simp [*]
    · apply IH

theorem list_getElem? : PrimrecIn₂ O (fun (l : List α) (n : ℕ) => l[n]?) := by
  convert list_get?
  ext
  simp

theorem list_getD (d : α) : PrimrecIn₂ O fun l n => List.getD l n d := by
  simp only [List.getD_eq_getElem?_getD]
  exact option_getD.comp₂ list_getElem? (const _)

theorem list_getI [Inhabited α] : PrimrecIn₂ O (@List.getI α _) :=
  list_getD _

theorem list_append : PrimrecIn₂ O ((· ++ ·) : List α → List α → List α) :=
  -- (list_foldr fst snd <| to₂ <| comp (@list_cons α _) snd).to₂.of_eq fun l₁ l₂ => by
  (list_foldr fst snd <| to₂ <| PrimrecIn.comp (list_cons) snd).to₂.of_eq fun l₁ l₂ => by
    induction l₁ <;> simp [*]

theorem list_concat : PrimrecIn₂ O fun l (a : α) => l ++ [a] :=
  list_append.comp fst (list_cons.comp snd (const []))

theorem list_map {f : α → List β} {g : α → β → σ} (hf : PrimrecIn O f) (hg : PrimrecIn₂ O g) :
    PrimrecIn O fun a => (f a).map (g a) :=
  (list_foldr hf (const []) <|
        to₂ <| list_cons.comp (hg.comp fst (fst.comp snd)) (snd.comp snd)).of_eq
    fun a => by induction f a <;> simp [*]

theorem list_range : PrimrecIn O List.range :=
  (nat_rec' .id (const []) ((list_concat.comp snd fst).comp snd).to₂).of_eq fun n => by
    simp; induction n <;> simp [*, List.range_succ]

theorem list_flatten : PrimrecIn O (@List.flatten α) :=
  -- (list_foldr .id (const []) <| to₂ <| comp (@list_append α _) snd).of_eq fun l => by
  (list_foldr .id (const []) <| to₂ <| PrimrecIn.comp (list_append) snd).of_eq fun l => by
    dsimp; induction l <;> simp [*]

@[deprecated (since := "2024-10-15")] alias list_join := list_flatten

theorem list_flatMap {f : α → List β} {g : α → β → List σ} (hf : PrimrecIn O f) (hg : PrimrecIn₂ O g) :
    PrimrecIn O (fun a => (f a).flatMap (g a)) := list_flatten.comp (list_map hf hg)

@[deprecated (since := "2024-10-16")] alias list_bind := list_flatMap

theorem optionToList : PrimrecIn O (Option.toList : Option α → List α) :=
  (option_casesOn PrimrecIn.id (const [])
    ((list_cons.comp PrimrecIn.id (const [])).comp₂ PrimrecIn₂.right)).of_eq
  (fun o => by rcases o <;> simp)

theorem listFilterMap {f : α → List β} {g : α → β → Option σ}
    (hf : PrimrecIn O f) (hg : PrimrecIn₂ O g) : PrimrecIn O fun a => (f a).filterMap (g a) :=
  (list_flatMap hf (comp₂ optionToList hg)).of_eq
    fun _ ↦ Eq.symm <| List.filterMap_eq_flatMap_toList _ _

theorem list_length : PrimrecIn O (@List.length α) :=
  -- (list_foldr (@PrimrecIn.id (List α) _) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
  --   fun l => by dsimp; induction l <;> simp [*]
  (list_foldr (PrimrecIn.id) (const 0) <| to₂ <| (succ.comp <| snd.comp snd).to₂).of_eq
    fun l => by dsimp; induction l <;> simp [*]

theorem list_findIdx {f : α → List β} {p : α → β → Bool}
    (hf : PrimrecIn O f) (hp : PrimrecIn₂ O p) : PrimrecIn O fun a => (f a).findIdx (p a) :=
  (list_foldr hf (const 0) <|
        to₂ <| cond (hp.comp fst <| fst.comp snd) (const 0) (succ.comp <| snd.comp snd)).of_eq
    fun a => by dsimp; induction f a <;> simp [List.findIdx_cons, *]

theorem list_idxOf [DecidableEq α] : PrimrecIn₂ O (@List.idxOf α _) :=
  to₂ <| list_findIdx snd <| PrimrecIn.beq.comp₂ snd.to₂ (fst.comp fst).to₂

@[deprecated (since := "2025-01-30")] alias list_indexOf := list_idxOf

theorem nat_strong_rec (f : α → ℕ → σ) {g : α → List σ → Option σ} (hg : PrimrecIn₂ O g)
    (H : ∀ a n, g a ((List.range n).map (f a)) = some (f a n)) : PrimrecIn₂ O f :=
  suffices PrimrecIn₂ O fun a n => (List.range n).map (f a) from
    PrimrecIn₂.option_some_iff.1 <|
      (list_get?.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq fun a n => by
        simp
  PrimrecIn₂.option_some_iff.1 <|
    (nat_rec (const (some []))
          (to₂ <|
            option_bind (snd.comp snd) <|
              to₂ <|
                option_map (hg.comp (fst.comp fst) snd)
                  (to₂ <| list_concat.comp (snd.comp fst) snd))).of_eq
      fun a n => by
      induction n with
      | zero => rfl
      | succ n IH => simp [IH, H, List.range_succ]

theorem listLookup [DecidableEq α] : PrimrecIn₂ O (List.lookup : α → List (α × β) → Option β) :=
  (to₂ <| list_rec snd (const none) <|
    to₂ <|
      cond (PrimrecIn.beq.comp (fst.comp fst) (fst.comp <| fst.comp snd))
        (option_some.comp <| snd.comp <| fst.comp snd)
        (snd.comp <| snd.comp snd)).of_eq
  fun a ps => by
  induction' ps with p ps ih <;> simp [List.lookup, *]
  cases ha : a == p.1 <;> simp [ha]

theorem nat_omega_rec' (f : β → σ) {m : β → ℕ} {l : β → List β} {g : β → List σ → Option σ}
    (hm : PrimrecIn O m) (hl : PrimrecIn O l) (hg : PrimrecIn₂ O g)
    (Ord : ∀ b, ∀ b' ∈ l b, m b' < m b)
    (H : ∀ b, g b ((l b).map f) = some (f b)) : PrimrecIn O f := by
  haveI : DecidableEq β := Encodable.decidableEqOfEncodable β
  let mapGraph (M : List (β × σ)) (bs : List β) : List σ := bs.flatMap (Option.toList <| M.lookup ·)
  let bindList (b : β) : ℕ → List β := fun n ↦ n.rec [b] fun _ bs ↦ bs.flatMap l
  let graph (b : β) : ℕ → List (β × σ) := fun i ↦ i.rec [] fun i ih ↦
    (bindList b (m b - i)).filterMap fun b' ↦ (g b' <| mapGraph ih (l b')).map (b', ·)
  have mapGraph_primrec : PrimrecIn₂ O mapGraph :=
    to₂ <| list_flatMap snd <| optionToList.comp₂ <| listLookup.comp₂ .right (fst.comp₂ .left)
  have bindList_primrec : PrimrecIn₂ O (bindList) :=
    nat_rec' snd
      (list_cons.comp fst (const []))
      (to₂ <| list_flatMap (snd.comp snd) (hl.comp₂ .right))
  have graph_primrec : PrimrecIn₂ O (graph) :=
    to₂ <| nat_rec' snd (const []) <|
      to₂ <| listFilterMap
        (bindList_primrec.comp
          (fst.comp fst)
          (nat_sub.comp (hm.comp <| fst.comp fst) (fst.comp snd))) <|
            to₂ <| option_map
              (hg.comp snd (mapGraph_primrec.comp (snd.comp <| snd.comp fst) (hl.comp snd)))
              (PrimrecIn₂.pair.comp₂ (snd.comp₂ .left) .right)
  have : PrimrecIn O (fun b => ((graph b (m b + 1)).get? 0).map Prod.snd) :=
    option_map (list_get?.comp (graph_primrec.comp PrimrecIn.id (succ.comp hm)) (const 0))
      (snd.comp₂ PrimrecIn₂.right)
  exact option_some_iff.mp <| this.of_eq <| fun b ↦ by
    have graph_eq_map_bindList (i : ℕ) (hi : i ≤ m b + 1) :
        graph b i = (bindList b (m b + 1 - i)).map fun x ↦ (x, f x) := by
      have bindList_eq_nil : bindList b (m b + 1) = [] :=
        have bindList_m_lt (k : ℕ) : ∀ b' ∈ bindList b k, m b' < m b + 1 - k := by
          induction' k with k ih <;> simp [bindList]
          intro a₂ a₁ ha₁ ha₂
          have : k ≤ m b :=
            Nat.lt_succ.mp (by simpa using Nat.add_lt_of_lt_sub <| Nat.zero_lt_of_lt (ih a₁ ha₁))
          have : m a₁ ≤ m b - k :=
            Nat.lt_succ.mp (by rw [← Nat.succ_sub this]; simpa using ih a₁ ha₁)
          exact lt_of_lt_of_le (Ord a₁ a₂ ha₂) this
        List.eq_nil_iff_forall_not_mem.mpr
          (by intro b' ha'; by_contra; simpa using bindList_m_lt (m b + 1) b' ha')
      have mapGraph_graph {bs bs' : List β} (has : bs' ⊆ bs) :
          mapGraph (bs.map <| fun x => (x, f x)) bs' = bs'.map f := by
        induction' bs' with b bs' ih <;> simp [mapGraph]
        · have : b ∈ bs ∧ bs' ⊆ bs := by simpa using has
          rcases this with ⟨ha, has'⟩
          simpa [List.lookup_graph f ha] using ih has'
      have graph_succ : ∀ i, graph b (i + 1) =
        (bindList b (m b - i)).filterMap fun b' =>
          (g b' <| mapGraph (graph b i) (l b')).map (b', ·) := fun _ => rfl
      have bindList_succ : ∀ i, bindList b (i + 1) = (bindList b i).flatMap l := fun _ => rfl
      induction' i with i ih
      · symm; simpa [graph] using bindList_eq_nil
      · simp only [graph_succ, ih (Nat.le_of_lt hi), Nat.succ_sub (Nat.lt_succ.mp hi),
          Nat.succ_eq_add_one, bindList_succ, Nat.reduceSubDiff]
        apply List.filterMap_eq_map_iff_forall_eq_some.mpr
        intro b' ha'; simp; rw [mapGraph_graph]
        · exact H b'
        · exact (List.infix_flatMap_of_mem ha' l).subset
    simp [graph_eq_map_bindList (m b + 1) (Nat.le_refl _), bindList]

theorem nat_omega_rec (f : α → β → σ) {m : α → β → ℕ}
    {l : α → β → List β} {g : α → β × List σ → Option σ}
    (hm : PrimrecIn₂ O m) (hl : PrimrecIn₂ O l) (hg : PrimrecIn₂ O g)
    (Ord : ∀ a b, ∀ b' ∈ l a b, m a b' < m a b)
    (H : ∀ a b, g a (b, (l a b).map (f a)) = some (f a b)) : PrimrecIn₂ O f :=
  PrimrecIn₂.uncurry.mp <|
    nat_omega_rec' (Function.uncurry f)
      (PrimrecIn₂.uncurry.mpr hm)
      (list_map (hl.comp fst snd) (PrimrecIn₂.pair.comp₂ (fst.comp₂ .left) .right))
      (hg.comp₂ (fst.comp₂ .left) (PrimrecIn₂.pair.comp₂ (snd.comp₂ .left) .right))
      (by simpa using Ord) (by simpa [Function.comp] using H)

end PrimrecIn

namespace Primcodable

variable {α : Type*} [Primcodable α]

open PrimrecIn

-- /-- A subtype of a primitive recursive predicate is `Primcodable`. -/
-- def subtype {p : α → Prop} [DecidablePred p] (hp : PrimrecInPred O p) : Primcodable (Subtype p) :=
--   ⟨have : PrimrecIn O fun n => (@decode α _ n).bind fun a => Option.guard p a :=
--     option_bind .decode (option_guard (hp.comp snd).to₂ snd)
--   nat_iff.1 <| (encode_iff.2 this).of_eq fun n =>
--     show _ = encode ((@decode α _ n).bind fun _ => _) by
--       rcases @decode α _ n with - | a; · rfl
--       dsimp [Option.guard]
--       by_cases h : p a <;> simp [h]; rfl⟩

-- instance fin {n} : Primcodable (Fin n) :=
--   @ofEquiv _ _ (subtype <| nat_lt.comp .id (const n)) Fin.equivSubtype

-- instance vector {n} : Primcodable (List.Vector α n) :=
--   subtype ((@PrimrecIn.eq ℕ _ _).comp list_length (const _))

-- instance finArrow {n} : Primcodable (Fin n → α) :=
--   ofEquiv _ (Equiv.vectorEquivFin _ _).symm


-- section ULower

-- attribute [local instance] Encodable.decidableRangeEncode Encodable.decidableEqOfEncodable

-- theorem mem_range_encode : PrimrecInPred O (fun n => n ∈ Set.range (encode : α → ℕ)) :=
--   have : PrimrecInPred O fun n => Encodable.decode₂ α n ≠ none :=
--     .not
--       (PrimrecIn.eq.comp
--         (.option_bind .decode
--           (.ite (PrimrecIn.eq.comp (PrimrecIn.encode.comp .snd) .fst)
--             (PrimrecIn.option_some.comp .snd) (.const _)))
--         (.const _))
--   this.of_eq fun _ => decode₂_ne_none_iff

-- instance ulower : Primcodable (ULower α) :=
--   Primcodable.subtype mem_range_encode

-- end ULower

end Primcodable

namespace PrimrecIn

-- variable {α : Type*} {β : Type*} {σ : Type*}
-- variable [Primcodable α] [Primcodable β] [Primcodable σ]

-- theorem subtype_val {p : α → Prop} [DecidablePred p] {hp : PrimrecInPred O p} :
--     haveI := Primcodable.subtype hp
--     PrimrecIn O (@Subtype.val α p) := by
--   letI := Primcodable.subtype hp
--   refine (@Primcodable.prim (Subtype p)).of_eq fun n => ?_
--   rcases @decode (Subtype p) _ n with (_ | ⟨a, h⟩) <;> rfl

-- theorem subtype_val_iff {p : β → Prop} [DecidablePred p] {hp : PrimrecInPred O p} {f : α → Subtype p} :
--     haveI := Primcodable.subtype hp
--     (PrimrecIn O fun a => (f a).1) ↔ PrimrecIn O f := by
--   letI := Primcodable.subtype hp
--   refine ⟨fun h => ?_, fun hf => subtype_val.comp hf⟩
--   refine Nat.PrimrecIn.of_eq h fun n => ?_
--   rcases @decode α _ n with - | a; · rfl
--   simp; rfl

-- theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecInPred O p} {f : α → β}
--     {h : ∀ a, p (f a)} (hf : PrimrecIn O f) :
--     haveI := Primcodable.subtype hp
--     PrimrecIn O fun a => @Subtype.mk β p (f a) (h a) :=
--   subtype_val_iff.1 hf

-- theorem option_get {f : α → Option β} {h : ∀ a, (f a).isSome} :
--     PrimrecIn O f → PrimrecIn O fun a => (f a).get (h a) := by
--   intro hf
--   refine (Nat.PrimrecIn.pred.comp hf).of_eq fun n => ?_
--   generalize hx : @decode α _ n = x
--   cases x <;> simp

-- theorem ulower_down : PrimrecIn O (ULower.down : α → ULower α) :=
--   letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidableRangeEncode _
--   subtype_mk .encode

-- theorem ulower_up : PrimrecIn O (ULower.up : ULower α → α) :=
--   letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidableRangeEncode _
--   option_get (PrimrecIn.decode₂.comp subtype_val)

-- theorem fin_val_iff {n} {f : α → Fin n} : (PrimrecIn O fun a => (f a).1) ↔ PrimrecIn O f := by
--   letI : Primcodable { a // id a < n } := Primcodable.subtype (nat_lt.comp .id (const _))
--   exact (Iff.trans (by rfl) subtype_val_iff).trans (of_equiv_iff _)

-- theorem fin_val {n} : PrimrecIn O (fun (i : Fin n) => (i : ℕ)) :=
--   fin_val_iff.2 .id

-- theorem fin_succ {n} : PrimrecIn O (@Fin.succ n) :=
--   fin_val_iff.1 <| by simp [succ.comp fin_val]

-- theorem vector_toList {n} : PrimrecIn O (@List.Vector.toList α n) :=
--   subtype_val

-- theorem vector_toList_iff {n} {f : α → List.Vector β n} :
--     (PrimrecIn O fun a => (f a).toList) ↔ PrimrecIn O f :=
--   subtype_val_iff

-- theorem vector_cons {n} : PrimrecIn₂ O (@List.Vector.cons α n) :=
--   vector_toList_iff.1 <| by simpa using list_cons.comp fst (vector_toList_iff.2 snd)

-- theorem vector_length {n} : PrimrecIn O (@List.Vector.length α n) :=
--   const _

-- theorem vector_head {n} : PrimrecIn O (@List.Vector.head α n) :=
--   option_some_iff.1 <| (list_head?.comp vector_toList).of_eq fun ⟨_ :: _, _⟩ => rfl

-- theorem vector_tail {n} : PrimrecIn O (@List.Vector.tail α n) :=
--   vector_toList_iff.1 <| (list_tail.comp vector_toList).of_eq fun ⟨l, h⟩ => by cases l <;> rfl

-- theorem vector_get {n} : PrimrecIn₂ O (@List.Vector.get α n) :=
--   option_some_iff.1 <|
--     (list_get?.comp (vector_toList.comp fst) (fin_val.comp snd)).of_eq fun a => by
--       rw [Vector.get_eq_get_toList, ← List.get?_eq_get]
--       rfl

-- theorem list_ofFn :
--     ∀ {n} {f : Fin n → α → σ}, (∀ i, PrimrecIn O (f i)) → PrimrecIn O fun a => List.ofFn fun i => f i a
--   | 0, _, _ => by simp only [List.ofFn_zero]; exact const []
--   | n + 1, f, hf => by
--     simpa [List.ofFn_succ] using list_cons.comp (hf 0) (list_ofFn fun i => hf i.succ)

-- theorem vector_ofFn {n} {f : Fin n → α → σ} (hf : ∀ i, PrimrecIn O (f i)) :
--     PrimrecIn O fun a => List.Vector.ofFn fun i => f i a :=
--   vector_toList_iff.1 <| by simp [list_ofFn hf]

-- theorem vector_get' {n} : PrimrecIn O (@List.Vector.get α n) :=
--   of_equiv_symm

-- theorem vector_ofFn' {n} : PrimrecIn O (@List.Vector.ofFn α n) :=
--   of_equiv

-- theorem fin_app {n} : PrimrecIn₂ O (@id (Fin n → σ)) :=
--   (vector_get.comp (vector_ofFn'.comp fst) snd).of_eq fun ⟨v, i⟩ => by simp

-- theorem fin_curry₁ {n} {f : Fin n → α → σ} : PrimrecIn₂ O f ↔ ∀ i, PrimrecIn O (f i) :=
--   ⟨fun h i => h.comp (const i) .id, fun h =>
--     (vector_get.comp ((vector_ofFn h).comp snd) fst).of_eq fun a => by simp⟩

-- theorem fin_curry {n} {f : α → Fin n → σ} : PrimrecIn O f ↔ PrimrecIn₂ O f :=
--   ⟨fun h => fin_app.comp (h.comp fst) snd, fun h =>
--     (vector_get'.comp
--           (vector_ofFn fun i => show PrimrecIn O fun a => f a i from h.comp .id (const i))).of_eq
--       fun a => by funext i; simp⟩

-- end PrimrecIn O

-- namespace Nat

-- open List.Vector

-- /-- An alternative inductive definition of `PrimrecIn O` which
--   does not use the pairing function on ℕ, and so has to
--   work with n-ary functions on ℕ instead of unary functions.
--   We prove that this is equivalent to the regular notion
--   in `to_prim` and `of_prim`. -/
-- inductive PrimrecIn O' : ∀ {n}, (List.Vector ℕ n → ℕ) → Prop
--   | zero : @PrimrecIn O' 0 fun _ => 0
--   | succ : @PrimrecIn O' 1 fun v => succ v.head
--   | get {n} (i : Fin n) : PrimrecIn O' fun v => v.get i
--   | comp {m n f} (g : Fin n → List.Vector ℕ m → ℕ) :
--       PrimrecIn O' f → (∀ i, PrimrecIn O' (g i)) → PrimrecIn O' fun a => f (List.Vector.ofFn fun i => g i a)
--   | prec {n f g} :
--       @PrimrecIn O' n f →
--         @PrimrecIn O' (n + 2) g →
--           PrimrecIn O' fun v : List.Vector ℕ (n + 1) =>
--             v.head.rec (f v.tail) fun y IH => g (y ::ᵥ IH ::ᵥ v.tail)

-- end Nat

-- namespace Nat.PrimrecIn O'

-- open List.Vector PrimrecIn O

-- theorem to_prim {n f} (pf : @Nat.PrimrecIn O' n f) : PrimrecIn O f := by
--   induction pf with
--   | zero => exact .const 0
--   | succ => exact _root_.PrimrecIn.succ.comp .vector_head
--   | get i => exact PrimrecIn.vector_get.comp .id (.const i)
--   | comp _ _ _ hf hg => exact hf.comp (.vector_ofFn fun i => hg i)
--   | @prec n f g _ _ hf hg =>
--     exact
--       .nat_rec' .vector_head (hf.comp PrimrecIn.vector_tail)
--         (hg.comp <|
--           PrimrecIn.vector_cons.comp (PrimrecIn.fst.comp .snd) <|
--           PrimrecIn.vector_cons.comp (PrimrecIn.snd.comp .snd) <|
--             (@PrimrecIn.vector_tail _ _ (n + 1)).comp .fst).to₂

-- theorem of_eq {n} {f g : List.Vector ℕ n → ℕ} (hf : PrimrecIn O' f) (H : ∀ i, f i = g i) :
--     PrimrecIn O' g :=
--   (funext H : f = g) ▸ hf

-- theorem const {n} : ∀ m, @PrimrecIn O' n fun _ => m
--   | 0 => zero.comp Fin.elim0 fun i => i.elim0
--   | m + 1 => succ.comp _ fun _ => const m

-- theorem head {n : ℕ} : @PrimrecIn O' n.succ head :=
--   (get 0).of_eq fun v => by simp [get_zero]

-- theorem tail {n f} (hf : @PrimrecIn O' n f) : @PrimrecIn O' n.succ fun v => f v.tail :=
--   (hf.comp _ fun i => @get _ i.succ).of_eq fun v => by
--     rw [← ofFn_get v.tail]; congr; funext i; simp

-- /-- A function from vectors to vectors is primitive recursive when all of its projections are. -/
-- def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) : Prop :=
--   ∀ i, PrimrecIn O' fun v => (f v).get i

-- protected theorem nil {n} : @Vec n 0 fun _ => nil := fun i => i.elim0

-- protected theorem cons {n m f g} (hf : @PrimrecIn O' n f) (hg : @Vec n m g) :
--     Vec fun v => f v ::ᵥ g v := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i

-- theorem idv {n} : @Vec n n id :=
--   get

-- theorem comp' {n m f g} (hf : @PrimrecIn O' m f) (hg : @Vec n m g) : PrimrecIn O' fun v => f (g v) :=
--   (hf.comp _ hg).of_eq fun v => by simp

-- theorem comp₁ (f : ℕ → ℕ) (hf : @PrimrecIn O' 1 fun v => f v.head) {n g} (hg : @PrimrecIn O' n g) :
--     PrimrecIn O' fun v => f (g v) :=
--   hf.comp _ fun _ => hg

-- theorem comp₂ (f : ℕ → ℕ → ℕ) (hf : @PrimrecIn O' 2 fun v => f v.head v.tail.head) {n g h}
--     (hg : @PrimrecIn O' n g) (hh : @PrimrecIn O' n h) : PrimrecIn O' fun v => f (g v) (h v) := by
--   simpa using hf.comp' (hg.cons <| hh.cons PrimrecIn O'.nil)

-- theorem prec' {n f g h} (hf : @PrimrecIn O' n f) (hg : @PrimrecIn O' n g) (hh : @PrimrecIn O' (n + 2) h) :
--     @PrimrecIn O' n fun v => (f v).rec (g v) fun y IH : ℕ => h (y ::ᵥ IH ::ᵥ v) := by
--   simpa using comp' (prec hg hh) (hf.cons idv)

-- theorem pred : @PrimrecIn O' 1 fun v => v.head.pred :=
--   (prec' head (const 0) head).of_eq fun v => by simp; cases v.head <;> rfl

-- theorem add : @PrimrecIn O' 2 fun v => v.head + v.tail.head :=
--   (prec head (succ.comp₁ _ (tail head))).of_eq fun v => by
--     simp; induction v.head <;> simp [*, Nat.succ_add]

-- theorem sub : @PrimrecIn O' 2 fun v => v.head - v.tail.head := by
--   have : @PrimrecIn O' 2 fun v ↦ (fun a b ↦ b - a) v.head v.tail.head := by
--     refine (prec head (pred.comp₁ _ (tail head))).of_eq fun v => ?_
--     simp; induction v.head <;> simp [*, Nat.sub_add_eq]
--   simpa using comp₂ (fun a b => b - a) this (tail head) head

-- theorem mul : @PrimrecIn O' 2 fun v => v.head * v.tail.head :=
--   (prec (const 0) (tail (add.comp₂ _ (tail head) head))).of_eq fun v => by
--     simp; induction v.head <;> simp [*, Nat.succ_mul]; rw [add_comm]

-- theorem if_lt {n a b f g} (ha : @PrimrecIn O' n a) (hb : @PrimrecIn O' n b) (hf : @PrimrecIn O' n f)
--     (hg : @PrimrecIn O' n g) : @PrimrecIn O' n fun v => if a v < b v then f v else g v :=
--   (prec' (sub.comp₂ _ hb ha) hg (tail <| tail hf)).of_eq fun v => by
--     cases e : b v - a v
--     · simp [not_lt.2 (Nat.sub_eq_zero_iff_le.mp e)]
--     · simp [Nat.lt_of_sub_eq_succ e]

-- theorem natPair : @PrimrecIn O' 2 fun v => v.head.pair v.tail.head :=
--   if_lt head (tail head) (add.comp₂ _ (tail <| mul.comp₂ _ head head) head)
--     (add.comp₂ _ (add.comp₂ _ (mul.comp₂ _ head head) head) (tail head))

-- protected theorem encode : ∀ {n}, @PrimrecIn O' n encode
--   | 0 => (const 0).of_eq fun v => by rw [v.eq_nil]; rfl
--   | _ + 1 =>
--     (succ.comp₁ _ (natPair.comp₂ _ head (tail PrimrecIn O'.encode))).of_eq fun ⟨_ :: _, _⟩ => rfl

-- theorem sqrt : @PrimrecIn O' 1 fun v => v.head.sqrt := by
--   suffices H : ∀ n : ℕ, n.sqrt =
--       n.rec 0 fun x y => if x.succ < y.succ * y.succ then y else y.succ by
--     simp only [H, succ_eq_add_one]
--     have :=
--       @prec' 1 _ _
--         (fun v => by
--           have x := v.head; have y := v.tail.head
--           exact if x.succ < y.succ * y.succ then y else y.succ)
--         head (const 0) ?_
--     · exact this
--     have x1 : @PrimrecIn O' 3 fun v => v.head.succ := succ.comp₁ _ head
--     have y1 : @PrimrecIn O' 3 fun v => v.tail.head.succ := succ.comp₁ _ (tail head)
--     exact if_lt x1 (mul.comp₂ _ y1 y1) (tail head) y1
--   introv; symm
--   induction' n with n IH; · simp
--   dsimp; rw [IH]; split_ifs with h
--   · exact le_antisymm (Nat.sqrt_le_sqrt (Nat.le_succ _)) (Nat.lt_succ_iff.1 <| Nat.sqrt_lt.2 h)
--   · exact
--       Nat.eq_sqrt.2 ⟨not_lt.1 h, Nat.sqrt_lt.1 <| Nat.lt_succ_iff.2 <| Nat.sqrt_succ_le_succ_sqrt _⟩

-- theorem unpair₁ {n f} (hf : @PrimrecIn O' n f) : @PrimrecIn O' n fun v => (f v).unpair.1 := by
--   have s := sqrt.comp₁ _ hf
--   have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
--   refine (if_lt fss s fss s).of_eq fun v => ?_
--   simp [Nat.unpair]; split_ifs <;> rfl

-- theorem unpair₂ {n f} (hf : @PrimrecIn O' n f) : @PrimrecIn O' n fun v => (f v).unpair.2 := by
--   have s := sqrt.comp₁ _ hf
--   have fss := sub.comp₂ _ hf (mul.comp₂ _ s s)
--   refine (if_lt fss s s (sub.comp₂ _ fss s)).of_eq fun v => ?_
--   simp [Nat.unpair]; split_ifs <;> rfl

-- theorem of_prim {n f} : PrimrecIn O f → @PrimrecIn O' n f :=
--   suffices ∀ f, Nat.PrimrecIn O f → @PrimrecIn O' 1 fun v => f v.head from fun hf =>
--     (pred.comp₁ _ <|
--           (this _ hf).comp₁ (fun m => Encodable.encode <| (@decode (List.Vector ℕ n) _ m).map f)
--             PrimrecIn O'.encode).of_eq
--       fun i => by simp [encodek]
--   fun f hf => by
--   induction hf with
--   | zero => exact const 0
--   | succ => exact succ
--   | left => exact unpair₁ head
--   | right => exact unpair₂ head
--   | pair _ _ hf hg => exact natPair.comp₂ _ hf hg
--   | comp _ _ hf hg => exact hf.comp₁ _ hg
--   | prec _ _ hf hg =>
--     simpa using
--       prec' (unpair₂ head) (hf.comp₁ _ (unpair₁ head))
--         (hg.comp₁ _ <|
--           natPair.comp₂ _ (unpair₁ <| tail <| tail head) (natPair.comp₂ _ head (tail head)))

-- theorem prim_iff {n f} : @PrimrecIn O' n f ↔ PrimrecIn O f :=
--   ⟨to_prim, of_prim⟩

-- theorem prim_iff₁ {f : ℕ → ℕ} : (@PrimrecIn O' 1 fun v => f v.head) ↔ PrimrecIn O f :=
--   prim_iff.trans
--     ⟨fun h => (h.comp <| .vector_ofFn fun _ => .id).of_eq fun v => by simp, fun h =>
--       h.comp .vector_head⟩

-- theorem prim_iff₂ {f : ℕ → ℕ → ℕ} : (@PrimrecIn O' 2 fun v => f v.head v.tail.head) ↔ PrimrecIn₂ O f :=
--   prim_iff.trans
--     ⟨fun h => (h.comp <| PrimrecIn.vector_cons.comp .fst <|
--       PrimrecIn.vector_cons.comp .snd (.const nil)).of_eq fun v => by simp,
--     fun h => h.comp .vector_head (PrimrecIn.vector_head.comp .vector_tail)⟩

-- theorem vec_iff {m n f} : @Vec m n f ↔ PrimrecIn O f :=
--   ⟨fun h => by simpa using PrimrecIn.vector_ofFn fun i => to_prim (h i), fun h i =>
--     of_prim <| PrimrecIn.vector_get.comp h (.const i)⟩

-- end Nat.PrimrecIn O'

-- theorem PrimrecIn.nat_sqrt : PrimrecIn O Nat.sqrt :=
--   Nat.PrimrecIn O'.prim_iff₁.1 Nat.PrimrecIn O'.sqrt
