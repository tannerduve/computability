import Computability.TuringReductions
import Mathlib.Data.Option.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Nat.PSub
import Mathlib.Data.PFun
import Mathlib.Data.Part

open Denumerable
-- To Do: Need to write encoding for oracle partial recursive functions to define universal machine
-- and relativized versions of basic theorems (Mario's paper and Soare's book for reference).

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

def evalo (g : ℕ →. ℕ) : codeo → ℕ →. ℕ
| codeo.zero => pure 0
| codeo.succ => Nat.succ
| codeo.left => λ n => (Nat.unpair n).1
| codeo.right => λ n => (Nat.unpair n).2
| codeo.oracle => g
| codeo.pair cf cg => fun n => Nat.pair <$> evalo g cf n <*> evalo g cg n
| codeo.comp cf cg => λ n => (evalo g cg n >>= evalo g cf)
| codeo.prec cf cg =>
   Nat.unpaired fun a n =>
    n.rec (evalo g cf a) fun y IH => do
      let i ← IH
      evalo g cg (Nat.pair a (Nat.pair y i))
| codeo.rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> evalo g cf (Nat.pair a (n + m))).map (· + m)

def encode' : codeo → ℕ :=
λ c => match c with
| codeo.zero => 0
| codeo.succ => 1
| codeo.left => 2
| codeo.right => 3
| codeo.oracle => 4
| codeo.pair cf cg => 2 * (2 * Nat.pair (encode' cf) (encode' cg)) + 5
| codeo.comp cf cg => 2 * (2 * Nat.pair (encode' cf) (encode' cg) + 1) + 5
| codeo.prec cf cg => (2 * (2 * Nat.pair (encode' cf) (encode' cg)) + 1) + 5
| codeo.rfind' cf => (2 * (2 * encode' cf + 1) + 1) + 5

def decode' : ℕ → codeo
  | 0 => codeo.zero
  | 1 => codeo.succ
  | 2 => codeo.left
  | 3 => codeo.right
  | 4 => codeo.oracle
  | n + 5 =>
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, Nat.div2_val]
      apply lt_of_le_of_lt
      exact Nat.div_le_self (n / 2) 2
      apply lt_of_le_of_lt
      exact Nat.div_le_self n 2
      linarith
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => codeo.pair (decode' m.unpair.1) (decode' m.unpair.2)
    | false, true  => codeo.comp (decode' m.unpair.1) (decode' m.unpair.2)
    | true , false => codeo.prec (decode' m.unpair.1) (decode' m.unpair.2)
    | true , true  => codeo.rfind' (decode' m)

theorem encode'_decode' : ∀ c, encode' (decode' c) = c :=
λ c => match c with
  | 0 => by simp [encode', decode']
  | 1 => by simp [encode', decode']
  | 2 => by simp [encode', decode']
  | 3 => by simp [encode', decode']
  | 4 => by simp [encode', decode']
  | n + 5 => by
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, Nat.div2_val]
      apply lt_of_le_of_lt
      exact Nat.div_le_self (n / 2) 2
      apply lt_of_le_of_lt
      exact Nat.div_le_self n 2
      linarith
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode'_decode' m
    have IH1 := encode'_decode' m.unpair.1
    have IH2 := encode'_decode' m.unpair.2
    conv_rhs => rw [← Nat.bit_decomp n, ← Nat.bit_decomp n.div2]
    simp only [decode']
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [encode', decode', IH, IH1, IH2, Nat.bit_val]

instance denumCode : Denumerable codeo :=
  mk'
    ⟨encode', decode', fun c => by
        induction c <;> simp [encode', decode', Nat.div2_val, *],
    encode'_decode'⟩

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

-- /-- Partial functions `α → σ` between `Primcodable` types recursive in oracle g-/
-- def RecursiveInPrimcodable {α σ} [Primcodable α] [Primcodable σ] (g : ℕ →. ℕ) (f : α →. σ) :=
--   RecursiveIn g fun n => Part.bind (Encodable.decode (α := α) n) fun a => (f a).map Encodable.encode

-- /-- Partial functions `α → β → σ` between `Primcodable` types recursive in oracle g-/
-- def RecursiveInPrimcodable₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (g : ℕ →. ℕ) (f : α → β →. σ) :=
--   RecursiveInPrimcodable g fun p : α × β => f p.1 p.2

-- def ComputableIn {α σ} [Primcodable α] [Primcodable σ] (g : ℕ →. ℕ) (f : α →. σ) :=
--   RecursiveInPrimcodable g f

-- -- /-- Computable functions `α → β → σ` between `Primcodable` types -/
-- -- def Computable₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
-- --   Computable fun p : α × β => f p.1 p.2

-- def ComputableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (g : ℕ →. ℕ) (f : α → β → σ) :=
--   ComputableIn g (fun p : α × β => f p.1 p.2)

-- namespace RecursiveIn
-- variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
-- variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

-- theorem of_eq {f g h : ℕ →. ℕ} (hf : RecursiveIn h f) (H : ∀ n, f n = g n) : RecursiveIn h g :=
--   (funext H : f = g) ▸ hf

-- nonrec theorem comp₁ {f : β →. σ} {g : α → β} {h : ℕ →. ℕ} (hf : RecursiveInPrimcodable h f) (hg : @ComputableIn α β _ _ h g) :
--     RecursiveInPrimcodable h fun a => f (g a) :=
--   (hf.comp hg).of_eq fun n => by simp; cases' e : Encodable.decode (α := α) n with a <;> simp [e, Encodable.decode]

-- theorem nat_iff {f : ℕ →. ℕ} {g : ℕ →. ℕ} : RecursiveIn g f ↔ RecursiveInPrimcodable g f := by
--   simp [RecursiveInPrimcodable, Part.map_id']

-- end RecursiveIn

-- namespace RecursiveInPrimcodable₂
-- open RecursiveIn

-- variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
-- variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

-- theorem unpaired {f : ℕ → ℕ →. α} {g : ℕ →. ℕ} : RecursiveInPrimcodable g (Nat.unpaired f) ↔ RecursiveInPrimcodable₂ g f := by
--   simp [RecursiveInPrimcodable, RecursiveInPrimcodable₂, Part.map_id']

-- theorem unpaired' {f : ℕ → ℕ →. ℕ} {g : ℕ → ℕ} : RecursiveIn g (Nat.unpaired f) ↔ RecursiveInPrimcodable₂ g f := by
--   simp [nat_iff, unpaired]

-- -- nonrec theorem comp {f : β → γ →. σ} {g : α → β} {h : α → γ} {i : ℕ →. ℕ} (hf : RecursiveInPrimcodable₂ i f) (hg : @ComputableIn α β _ _ i g)
-- -- (hh : @ComputableIn α γ _ _ i h) :
-- --   RecursiveInPrimcodable i fun a => f (g a) (h a) := by
-- --   apply comp₁ hg hh

-- -- theorem comp₂ {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ} (hf : Partrec₂ f)
-- --     (hg : Computable₂ g) (hh : Computable₂ h) : Partrec₂ fun a b => f (g a b) (h a b) :=
-- --   hf.comp hg hh

-- -- theorem map {f : α →. β} {g : α → β → σ} (hf : Partrec f) (hg : Computable₂ g) :
-- --     Partrec fun a => (f a).map (g a) := by
-- --   simpa [bind_some_eq_map] using @Partrec.bind _ _ _ _ _ _ _ (fun a => Part.some ∘ (g a)) hf hg

-- theorem map {f : α →. β} {g : α → β → σ} {h : ℕ →. ℕ} (hf : RecursiveInPrimcodable h f) (hg : @ComputableIn₂ α β σ _ _ _ h g) :
--     RecursiveInPrimcodable h (fun a => (f a).map (g a)) := by
--   apply of_eq hf
--   intro n
--   simp [Part.map_id']

-- end RecursiveInPrimcodable₂



-- -- theorem rfind' {f} (hf : Nat.Partrec f) :
-- --     Nat.Partrec
-- --       (Nat.unpaired fun a m =>
-- --         (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m)) :=
-- --   Partrec₂.unpaired'.2 <| by
-- --     refine
-- --       Partrec.map
-- --         ((@Partrec₂.unpaired' fun a b : ℕ =>
-- --               Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + b))).1
-- --           ?_)
-- --         (Primrec.nat_add.comp Primrec.snd <| Primrec.snd.comp Primrec.fst).to_comp.to₂
-- --     have : Nat.Partrec (fun a => Nat.rfind (fun n => (fun m => decide (m = 0)) <$>
-- --       Nat.unpaired (fun a b => f (Nat.pair (Nat.unpair a).1 (b + (Nat.unpair a).2)))
-- --         (Nat.pair a n))) :=
-- --       rfind
-- --         (Partrec₂.unpaired'.2
-- --           ((Partrec.nat_iff.2 hf).comp
-- --               (Primrec₂.pair.comp (Primrec.fst.comp <| Primrec.unpair.comp Primrec.fst)
-- --                   (Primrec.nat_add.comp Primrec.snd
-- --                     (Primrec.snd.comp <| Primrec.unpair.comp Primrec.fst))).to_comp))
-- --     simpa
-- -- helper lemma to prove rfind' case of univ theorem, since rfind' is defined differently from rfind


-- lemma rfind' {f} (g : ℕ → ℕ) (hf : RecursiveIn g f) :
--     RecursiveIn g
--       (Nat.unpaired fun a m =>
--       (Nat.rfind fun n => (fun m => m = 0) <$> evalo g cf (Nat.pair a (n + m))).map (· + m)) :=
--       RecursiveInPrimcodable₂.unpaired'.2 <| by
--         refine
--           RecursiveIn.map


/-- A function is partial recursive relative to an oracle `g` if and only if there is a code implementing it.
Therefore, `evalo` is a **universal partial recursive function relative to `g`**. -/
theorem exists_code_rel {g : ℕ →. ℕ} {f : ℕ →. ℕ} : RecursiveIn g f ↔ ∃ c : codeo, evalo g c = f := by
  constructor
  · intro gf
    induction gf
    · exact ⟨codeo.zero, rfl⟩
    · exact ⟨codeo.succ, rfl⟩
    · exact ⟨codeo.left, rfl⟩
    · exact ⟨codeo.right, rfl⟩
    · exact ⟨codeo.oracle, rfl⟩
    · case mp.pair hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.pair cf cg, rfl⟩
    · case mp.comp hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.comp cf cg, rfl⟩
    · case mp.prec hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨codeo.prec cf cg, rfl⟩
    · case mp.rfind hf =>
      rcases hf with ⟨cf, rfl⟩
      refine ⟨codeo.comp (codeo.rfind' cf) (codeo.pair id_code codeo.zero), ?_⟩
      simp [evalo, Seq.seq, pure, PFun.pure, Part.map_id']
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
      sorry

def φ (g : ℕ →. ℕ) (e : ℕ) : ℕ →. ℕ :=
  evalo g (decode' e)
