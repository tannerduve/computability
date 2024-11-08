# Formalization of Oracle Computability and Turing Degrees in Lean

This project provides a **formalization of oracle computability and Turing degrees** in Lean, using **partial recursive functions with oracle access** as the model of computation. The focus is on formalizing relativized computability: computations that occur relative to an external oracle function, exploring their properties, and establishing the theory of Turing degrees. We build on existing work in the foundations of computability theory developed by Mario Carneiro [1] [2].

## Overview

### Oracle Computability

Oracle computability extends classical notions of computability by introducing an oracle: a function that a recursive function can query during computation. This allows us to analyze what functions are computable given access to different oracles. 

We define oracle-relative partial recursive functions with an inductive predicate `RecursiveIn`, The type of partial functions recursive in an oracle g is the smallest type containing the basic functions zero, successor, projections, and g itself, that is closed under pairing, composition, primitive recursion, and μ-minimization.

### Turing Reducibility and Turing Degrees

- **Turing Reducibility** (`≤ᵀ`): A function `f` is said to be Turing reducible to an oracle `g` if `f` can be computed by a partial recursive function with access to `g`.
- **Turing Equivalence** (`≡ᵀ`): Functions `f` and `g` are Turing equivalent if they are mutually Turing reducible. This defines an equivalence relation among functions, which allows us to form **Turing degrees** as equivalence classes under this relation.

Using Lean’s `Quot` type, we define **Turing degrees** as these equivalence classes, giving us a way of studying degrees of unsolvability via relativized computation.

## Key Components

1. **Recursive Functions with Oracle Access**: The `RecursiveIn` predicate is used to define relativized computability. The type of of partial functions recursive in a given partial function g (the oracle) is the smallest type containing the basic functions: the constant zero function, the successor function, the pairing function, the projection functions, and g itself, that is closed under composition, primitive recursion, and μ-minimization.
   
2. **Turing Reducibility (`≤ᵀ`) and Equivalence (`≡ᵀ`)**: These relations establish a notion of relative computability, allowing us to classify functions by their Turing degree.
   
3. **Turing Degrees**: Defined as quotient types under Turing equivalence, Turing degrees capture the classes of functions sharing the same oracle-relative computability.

4. **The Jump Operator**: The Jump operator (`jump`) maps functions to a higher Turing degree, increasing computational complexity. This operator is key to defining a hierarchy within Turing degrees.

5. **Encoding and Universal Oracle Machine**: We develop an encoding for oracle-based computations and define a universal partial recursive function relative to an oracle, enabling the representation and analysis of relativized computations within Lean.

## Roadmap

### Completed

- **Define Turing Reducibility**: Established `RecursiveIn` for functions relative to an oracle and defined Turing reducibility (`≤ᵀ`).
- **Prove Equivalence Relation**: Showed that Turing equivalence (`≡ᵀ`) is reflexive, symmetric, and transitive.
- **Define Turing Degrees**: Created `TuringDegree` as a quotient of functions under Turing equivalence.
- **Develop Encoding for Relativized Partial Recursive Functions**: Implemented `codeo`, `evalo`, and encoding/decoding functions to give a denumerable instance of codes for partial functions.
- **Define Jump Operator**: Introduced the Jump operator and started exploring its properties.

### In Progress

- **Theorem: The type of Turing degrees forms an upper semilattice**: Proving that when we lift turing reducibility and join to degrees, the resulting quotient type forms and upper semilattice, where the join of two functions is their supremum, and the reducibility relation is the partial ordering.
- **Relativize Key Theorems**: Proving that `evalo` serves as a universal relativized partial recursive function and establishing relativized versions of the fixed-point and Rice’s theorems.

### Next Steps
- **Prove Jump Theorems**: Establishing core properties of the Jump operator, such as relativized halting problem, and recursive enumerability in the function and strict non-reducibility.
- **Kleene-Post Theorem**: Demonstrating the existence of incomparable Turing degrees.

### Future Directions
- **Computational Complexity Theory**

## References
1. **Formalizing Computability Theory via Partial Recursive Functions**  
   Carneiro, Mario. [*Formalizing Computability Theory via Partial Recursive Functions.*](https://arxiv.org/pdf/1810.08380) *arXiv preprint arXiv:1810.08380,* 2018.  
   This paper explores the formalization of computability theory in Lean, providing insights and strategies that support the formalization efforts in this project.

2. **Lean `mathlib` Documentation on Partial Recursive Functions**  
   *Lean 4 mathlib documentation.*(https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Partrec.html#Computable).  
   This documentation provides details on the definitions and foundations of partial recursive functions in Lean's `mathlib`, which form the basis for defining computability in Lean.

3. **Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers, Vol. I**  
   Odifreddi, Piergiorgio. [*Classical Recursion Theory: The Theory of Functions and Sets of Natural Numbers, Vol. I.*](http://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT1.pdf) *Elsevier Science Ltd.,* 1989.  
   A comprehensive reference for recursion theory, covering foundational topics that inform the definitions and theorems formalized in this project.

4. **Recursively Enumerable Sets and Degrees**  
   Soare, Robert I. *Recursively Enumerable Sets and Degrees.* Springer-Verlag, 1987.  
   This book provides a detailed study of recursively enumerable sets and degrees, with in-depth discussions of the Turing degrees and the Jump operator, essential concepts in oracle computability.

5. **Turing Degrees**  
   Gu, Yi-Zhi. [*Turing Degrees.*](https://www.math.ias.edu/~yuzhougu/data/turing.pdf) Institute for Advanced Study, 2015.  
   This paper presents a survey of Turing degree theory, exploring the structure and properties of Turing degrees, which are central to understanding relativized computability and degrees of unsolvability.
