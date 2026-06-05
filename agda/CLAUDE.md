# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Agda mechanisation of the optimal constant-time amortisation bound for catenable queues, a puzzle from <https://github.com/koengit/puzzle2026>. The parent repo also contains a Haskell solver and a browser playground; this directory (`agda/`) is the proof development and is self-contained.

`Main.agda` is the top-level module that re-exports every theorem reaching the published statements: the amortisation upper bound (sufficiency of `kₐ = kₜ = 2`), the witness move sequence, its count formulas, the lower bound `kₐ + kₜ ≥ 4` (via `Necessary`), and the asymptotic `→ 4` approximation (via `Approx`).

## Build / type-check

This directory is an Agda library (`Main.agda-lib`, depends on `standard-library`). There is no Makefile.

```bash
# Type-check the whole development by checking the top-level module.
agda Main.agda

# Re-check a single file (its dependencies are re-checked on demand).
agda Sufficient.agda
```

The Agda standard library is located at `/Users/abel/project/open-source/agda-stdlib/src` and must be registered with Agda (via `~/.agda/libraries` / `~/.agda/defaults`) for the `depend: standard-library` line to resolve.

Every finished file ends with `{-# OPTIONS --safe #-}`. Do not introduce postulates, unsolved metas, or termination pragmas unless asked.

## Architecture

The development is built up in a strict dependency tower; later files only add a single concept at a time. Read them in this order if you are new:

1. **`Library.agda`** — project-wide re-exports of stdlib pieces and small utilities (`_>=>_`, iterated function `_^_`, `≤1+pred`). Open this rather than reaching into `Data.*` directly when possible.
2. **`Tree.agda`** — the binary tree datatype `Tree` with constructors `ε` and `_∙_`, the partial primitives `rotate`, `tail`, the auxiliary potential functions `Φₗ`, `Φᵣ`, the main potential `Φ`, and the `Resourced A` record (`n ⨮ a`) that pairs a payload with a natural-number resource counter. **Do not modify** `Tree.agda` or the statements of `amor-*` — they are fixed by the puzzle.
3. **`UpperBound.agda`** — proves `amor-append`, `amor-tail`, `amor-rotate`: the budget-2 amortisation inequalities for the three operations. The proofs go through a sandwich `Φᵣ ≤ Φ ≤ 1 + Φᵣ` and a small `max-lemma` for `amor-rotate`.
4. **`SingleTreeGame.agda`** — defines the inductive `Moves` (constructors `C`, `T`, `R`, `ε`, `_∙_`) and its semantics `moves : Moves → Tree → Maybe Tree`. Also a Cayley-form `M = Moves → Moves` with combinators `c`, `t`, `r` used to build long move sequences readably.
5. **`Sequence.agda`** — constructs the witness move sequence `seq m n` whose `R/C` ratio approaches 4 (`start n ∘ (loop n)^m ∘ unravel n`) and proves `thm-seq : move (seq m n) ε ≡ just ε`. Uses suffix-aware lemmas (`*-suf`) per fragment (`cr`, `crtrr`, `crtr`, `tr`) so that proofs compose.
6. **`Counting.agda`** — count records `MoveCounts = C: c# T: t# R: r#` and the structural counting lemmas mirroring `Sequence.agda`. The pay-off `thm-counts-seq` gives closed-form counts `c# = t# = m·(n+2) + n + 3` and `r# = m·(4n+3) + 3n + 2`.
7. **`ResourcedSingleTreeGame.agda`** — `RT = Resourced Tree`, the resourced executor `RMoves.rmoves` parameterised by budgets `kₐ kₜ`, plus `thm-counts` / `thm-counts'` linking executed moves to the inequality `r# + n' ≤ c# · kₐ + (t# · kₜ + n)`.
8. **`SufficientSingleTree.agda`** — proves that `kₐ = kₜ = 2` suffice on a single tree (by induction on `Moves` via `Legal`).
9. **`Necessary.agda`** — uses `seq 1 11` (which has `r# = 82`, `c# = t# = 27`) to derive a contradiction from `kₐ + kₜ ≤ 3`, hence `kₐ + kₜ ≥ 4` is necessary.
10. **`Approx.agda`** — strengthens the bound: for every `N` exhibits `p, q` with `q ≥ N·p` and `q·(kₐ+kₜ) + p ≥ 4q`, using `seq (14N) (14N)`.
11. **`MultiTreeGame.agda`** — generalises from a single tree to a `Forest n = Vec Tree n`. Moves are typed by their arity transition: `U : Moves m (1+m)` (insert empty), `C i j : Moves (1+m) m` (concat two picked trees), `R i`, `T i` (act on tree at index `i`). `pick` returns the selected tree together with the remaining forest. `RMoves.rmoves` is the resourced executor over forests.
12. **`Sufficient.agda`** — the forest-level analogue of `SufficientSingleTree.agda`. Has extra structural lemmas (`pick-view`, `concat-budget`, `tail-budget-forest`, `rotate-budget-forest`) because each move first projects out the affected tree from `Φs`.
13. **`Main.agda`** — re-states the headline theorems (`amortization`, `move-sequence`, `resourced`, `counting`, `necessary`, `approximation`) in terms of the chosen constants `kₐ = kₜ = 2`. This is the file to update when a downstream theorem's interface changes.

### Cross-cutting conventions

- **Two-step proofs**: each structural file pairs a top-level theorem (`thm-foo`) with a `thm-foo-suf` or `lem-foo-suf` "suffix" form that takes an extra continuation `ms`. The suffixed forms are what compose; the unsuffixed forms instantiate with `ms = ε`. Preserve this pattern when extending.
- **Legality + budget invariant**: in both `SufficientSingleTree` and `Sufficient`, `Legal mv (n ⨮ ts) (n' ⨮ ts') = rmoves mv ≡ just ... × n' + Φs ts ≥ n + Φs ts'`. The induction step composes two such inequalities via the local `compose-sum-inequalities` lemma — duplicate, do not factor out, unless asked.
- **Counts vs. budgets**: `Counting`/`thm-counts-seq` produce the closed-form counts; `ResourcedSingleTreeGame.thm-counts` converts a successful resourced run into the inequality `r# + n' ≤ c# · kₐ + (t# · kₜ + n)`. The lower-bound proofs (`Necessary`, `Approx`) only use this inequality, not the executor's internals.

## Proof-style guidance (from `.github/instructions/agda.instructions.md`)

- Work surgically: do not modify definitions, theorem statements, proof structure, or layout unless the prompt asks for it. If a stated theorem is false or ill-typed, alert the user and propose a fix rather than silently changing it.
- Prefer `≤-Reasoning` chains for inequalities. Use `≡-Reasoning` only for genuinely non-trivial equalities that no solver can dispatch in one step.
- For routine arithmetic over `ℕ`, prefer Agda stdlib solvers over hand-written equation chains. `Data.Nat.Solver.+-*-Solver.solve` and `Data.Nat.Tactic.RingSolver.solve-∀` are both used in this project — pick whichever discharges the equation in one line.
- Use named helper lemmas for structural facts; reserve low-level `rewrite` / `subst` for places where neither a solver nor an existing lemma fits.
- When proving count or resource bounds, first normalise the statement into the shape best suited for `≤-Reasoning`, then use solver-backed `≡⟨ ... ⟩` steps only at the arithmetic transitions.
- Useful stdlib modules already wired up in this project: `Data.Nat.Properties`, `Data.Nat.Solver`, `Data.Nat.Tactic.RingSolver`, `Relation.Binary.PropositionalEquality`.
- A previous run blew up Agda's memory by feeding very large expressions to `rewrite`. When a step looks large, prefer `≤-Reasoning` / `≡-Reasoning` chains with the solver doing the heavy lifting over one huge `rewrite`.

## Project history (`prompt.md`)

`prompt.md` is a hand-curated log of prior prompts and their outcomes. It documents (a) earlier statements that turned out to be false and were corrected (e.g. the original `amor-*` had wrong constants), (b) which constants are minimal (`kₐ = kₜ = 2` in `Tree`-level `Φ`), and (c) why certain count formulas were corrected (the original `c#`/`t#` overcounted by `3m`). Skim it before changing a long-standing statement — chances are the formulation has already been argued over.
