import Computability.SingleOracle.Oracle

open List (Vector)
open Encodable Denumerable Part






namespace RecursiveIn
open Nat in
theorem ppred : RecursiveIn O fun n => ppred n :=
  have : Primrec₂ fun n m => if n = Nat.succ m then 0 else 1 :=
    (Primrec.ite
      (@PrimrecRel.comp _ _ _ _ _ _ _ _ _ _
        Primrec.eq Primrec.fst (_root_.Primrec.succ.comp Primrec.snd))
      (_root_.Primrec.const 0) (_root_.Primrec.const 1)).to₂
  (of_primrec (Primrec₂.unpaired'.2 this)).rfind.of_eq fun n => by
    cases n <;> simp
    · exact
        eq_none_iff.2 fun a ⟨⟨m, h, _⟩, _⟩ => by
          simp only [mem_some_iff, Bool.true_eq_false] at h
    · refine eq_some_iff.2 ?_
      simp only [mem_rfind, decide_true, mem_some_iff,
        false_eq_decide_iff, true_and]
      intro m h
      exact Nat.ne_of_lt' h

end RecursiveIn













namespace ComputableIn

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]

theorem of_eq {f g : α → σ} (hf : ComputableIn O f) (H : ∀ n, f n = g n) : ComputableIn O g :=
  (funext H : f = g) ▸ hf

theorem const (s : σ) : ComputableIn O fun _ : α => s :=
  (Primrec.const _).to_computableIn

theorem ofOption {f : α → Option β} (hf : ComputableIn O f) : RecursiveIn' O fun a => (f a : Part β) :=
  (RecursiveIn.ppred.comp hf).of_eq fun n => by
    simp only [liftPrim, map_some, bind_eq_bind]
    rcases decode (α := α) n with - | a <;> simp
    rcases f a with - | b <;> simp

theorem to₂ {f : α × β → σ} (hf : ComputableIn O f) : Computable₂ fun a b => f (a, b) :=
  hf.of_eq fun ⟨_, _⟩ => rfl

protected theorem id : ComputableIn O (@id α) :=
  Primrec.id.to_computableIn

theorem fst : ComputableIn O (@Prod.fst α β) :=
  Primrec.fst.to_computableIn

theorem snd : ComputableIn O (@Prod.snd α β) :=
  Primrec.snd.to_computableIn

nonrec theorem pair {f : α → β} {g : α → γ} (hf : ComputableIn O f) (hg : ComputableIn O g) :
    ComputableIn O fun a => (f a, g a) :=
  (hf.pair hg).of_eq fun n => by cases decode (α := α) n <;> simp [Seq.seq]

theorem unpair : ComputableIn O Nat.unpair :=
  Primrec.unpair.to_computableIn

theorem succ : ComputableIn O Nat.succ :=
  Primrec.succ.to_computableIn

theorem pred : ComputableIn O Nat.pred :=
  Primrec.pred.to_computableIn

theorem nat_bodd : ComputableIn O Nat.bodd :=
  Primrec.nat_bodd.to_computableIn

theorem nat_div2 : ComputableIn O Nat.div2 :=
  Primrec.nat_div2.to_computableIn

theorem sumInl : ComputableIn O (@Sum.inl α β) :=
  Primrec.sumInl.to_computableIn

theorem sumInr : ComputableIn O (@Sum.inr α β) :=
  Primrec.sumInr.to_computableIn

@[deprecated (since := "2025-02-21")] alias sum_inl := ComputableIn O.sumInl
@[deprecated (since := "2025-02-21")] alias sum_inr := ComputableIn O.sumInr

theorem list_cons : Computable₂ (@List.cons α) :=
  Primrec.list_cons.to_computableIn

theorem list_reverse : ComputableIn O (@List.reverse α) :=
  Primrec.list_reverse.to_computableIn

theorem list_get? : Computable₂ (@List.get? α) :=
  Primrec.list_get?.to_computableIn

theorem list_append : Computable₂ ((· ++ ·) : List α → List α → List α) :=
  Primrec.list_append.to_computableIn

theorem list_concat : Computable₂ fun l (a : α) => l ++ [a] :=
  Primrec.list_concat.to_computableIn

theorem list_length : ComputableIn O (@List.length α) :=
  Primrec.list_length.to_computableIn

theorem vector_cons {n} : Computable₂ (@List.Vector.cons α n) :=
  Primrec.vector_cons.to_computableIn

theorem vector_toList {n} : ComputableIn O (@List.Vector.toList α n) :=
  Primrec.vector_toList.to_computableIn

theorem vector_length {n} : ComputableIn O (@List.Vector.length α n) :=
  Primrec.vector_length.to_computableIn

theorem vector_head {n} : ComputableIn O (@List.Vector.head α n) :=
  Primrec.vector_head.to_computableIn

theorem vector_tail {n} : ComputableIn O (@List.Vector.tail α n) :=
  Primrec.vector_tail.to_computableIn

theorem vector_get {n} : Computable₂ (@List.Vector.get α n) :=
  Primrec.vector_get.to_computableIn

theorem vector_ofFn' {n} : ComputableIn O (@List.Vector.ofFn α n) :=
  Primrec.vector_ofFn'.to_computableIn

theorem fin_app {n} : Computable₂ (@id (Fin n → σ)) :=
  Primrec.fin_app.to_computableIn

protected theorem encode : ComputableIn O (@encode α _) :=
  Primrec.encode.to_computableIn

protected theorem decode : ComputableIn O (decode (α := α)) :=
  Primrec.decode.to_computableIn

protected theorem ofNat (α) [Denumerable α] : ComputableIn O (ofNat α) :=
  (Primrec.ofNat _).to_computableIn

theorem encode_iff {f : α → σ} : (ComputableIn O fun a => encode (f a)) ↔ ComputableIn O f :=
  Iff.rfl

theorem option_some : ComputableIn O (@Option.some α) :=
  Primrec.option_some.to_computableIn

end ComputableIn O
