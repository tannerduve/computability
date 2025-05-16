# Oracle Computability and Turing Degrees in Lean

This project formalizes **oracle-relative computability** and the **theory of Turing degrees** in Lean. It defines relativized partial recursive functions, formalizes Turing reducibility and equivalence, constructs the Turing degrees as a quotient type, and explores structural properties including the join operation and jump operator.

## Key Modules

### `Oracle.lean`
Defines relativized partial recursive functions:
- `RecursiveIn O f`: the function `f` is computable relative to oracles in the set `O`.
- Variants: `RecursiveIn'`, `RecursiveIn₂`, `ComputableIn`, `ComputableIn₂` for functions between `Primcodable` types.
- Lifting functions using `Primcodable` encoding.

### `TuringDegree.lean`
Builds Turing reducibility and degree structure:
- `f ≤ᵀ g`: `f` is recursive in `g`.
- `f ≡ᵀ g`: mutual reducibility.
- `TuringDegree`: equivalence classes of `ℕ →. ℕ` under `≡ᵀ`.
- Proof that `TuringDegree` is a partial order
- Defines `turingJoin` (`f ⊕ g`) as supremum of partial functions `ℕ →. ℕ`
- Join lemmas (`left_le_join`, `right_le_join`, `join_le`, ie. join is supremum) are stated with `sorry`

### `Encoding.lean`
Godel numbering for partial recursive functions with oracle sets indexed by a primcodable type
Implements universal oracle machine `evalo`:
- Universality: `RecursiveIn (range g) f ↔ ∃ c, evalo g c = f`.
- Encoding/decoding via `encodeCodeo` and `decodeCodeo`

### `AutGrp.lean`
Defines the automorphism group of the Turing degrees:
- `TuringDegree.automorphismGroup := OrderAut TuringDegree`
- Group operations from `OrderIso`.
- `Countable` instance is conjectured (`sorry`).

### `ReductionDSL.lean`
Would like to write a DSL for writing reductions that compiles into `RecursiveIn` proofs. Unimplemented currently.

## In Progress
- Show that `TuringDegree` forms an upper semilattice.
- Complete the proof that `encodeCodeo ∘ decodeCodeo = id`.

## Project Directions
- Build a real DSL for writing reductions (`ReductionDSL.lean`)
- Prove countability of automorphism group for Turing degrees
- Formalize a priority argument (eg. Kleene-Post theorem)

## References

1. Mario Carneiro. [*Formalizing Computability Theory via Partial Recursive Functions*](https://arxiv.org/pdf/1810.08380), arXiv:1810.08380, 2018.
2. Piergiorgio Odifreddi. *Classical Recursion Theory*, Vol. I. [PDF](http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT1.pdf)

## 📂 License

Apache 2.0 © 2025 Tanner Duve, Elan Roth
