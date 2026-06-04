
Agent instructions for the Agda proofs in this project:

1. Work surgically. Preserve definitions, theorem statements, proof structure, and layout unless the prompt explicitly asks for broader changes.
2. For Agda proof development, prefer `≤-Reasoning` chains for inequalities. Use `≡-Reasoning` only for genuinely nontrivial equalities that cannot be discharged directly by the standard-library solver.
3. When an arithmetic equality over naturals is routine, prefer Agda stdlib solvers instead of hand-written `≡-Reasoning` chains. In this project, `Data.Nat.Solver.+-*-Solver.solve` is the preferred tool for polynomial rearrangements.
4. Keep proof steps readable: use named helper lemmas for structural facts, and reserve low-level rewrites for places where neither a solver nor an existing lemma gives a clear one-step proof.
5. When proving bounds on move counts or resources, first normalize the statement into the form best suited for a `≤-Reasoning` chain, then use solver-backed equality steps only at the arithmetic transitions.
6. End finished Agda files with `{-# OPTIONS --safe #-}` and avoid postulates, unsolved metas, and termination pragmas unless explicitly requested.
7. The Agda standard library used in this environment has been found at:
   `/Users/abel/project/open-source/agda-stdlib/src`
8. Useful standard-library modules already used successfully in this project include:
   - `Data.Nat.Properties`
   - `Data.Nat.Solver`
   - `Relation.Binary.PropositionalEquality`
