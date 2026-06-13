
<link rel="stylesheet" href="gh-fork-ribbon.css" />
<style>.github-fork-ribbon:before { background-color: #333; }</style>
<a class="github-fork-ribbon" href="https://github.com/andreasabel/tree-rotation" data-ribbon="Sources on GitHub" title="Sources on GitHub">Sources on GitHub</a>

tree-rotation
=============

Leaf-labelled binary trees are amortized constant-time queues.

Initiated by the puzzle at: https://github.com/koengit/puzzle2026

This repository contains the following components:

1. A [paper](tex/main.pdf) proving that leaf-labelled binary trees are amortized constant-time queues.
2. A [rendered](agda/html/Main.html) [Agda formalization](agda/Main.agda) of the definitions, theorems, and proofs.
3. A [browser playground](play/index.html) for interactively stepping through move sequences and visualizing the resulting tree.
4. A Haskell program, [`tree-rotation`](tree-rotation.cabal), for highest rotations per constructors ratio search and plotting.

The project is licensed under the **BSD 3-clause license**; see [LICENSE](LICENSE).

## Agda code

The [code](agda/Main.agda) needs requires Agda standard library v2.4.
It has been tested with Agda 2.8.0 and 2.9.0.

## Web playground

The interactive page lives at [play/index.html](play/index.html).

It is a self-contained visualization of the tree-rotation game. The page shows:

- the current counts of concatenation (`C`), tail (`T`), and rotation (`R`) moves and the ratio `R/C`,
- an SVG rendering of the current tree, omitting leaf nodes,
- a input field for the move sequence that drives the whole display.

### How to play

Open `play/index.html` in a browser, then type a move string such as `ccrtt` into the input field.

- `c` appends a leaf on the right, consuming one available concatenation move,
- `r` performs a tree rotation when the current tree has the right shape,
- `t` takes the tail when the left subtree of the current tree is a leaf (displayed as absent).

The displayed tree and score is determined by the moves up to the current cursor position.
Thus, you can step backward and forward through a longer sequence and inspect intermediate states without deleting text.
If the move sequence is illegal, the tree pane shows a large red `X`.

## Command-line solver in Haskell

The executable **`tree-rotation`** solves the game by exhaustive exploration of the game tree.

By default it solves the game for the number `N` of concatenation moves, starting at `N = 1`, and keeps running for `N, N+1, N+2, ...` until interrupted. For each solved `N`, it prints the winner, i.e., the move sequence with the most rotations, and appends a CSV row with

```text
n,score,ratio,iterations,moves
```

where `score` is the number of rotations, `ratio` is `score / n`, `iterations` is the search-specific work counter, and `moves` is the winning move trail.

### Search modes

- **Exact search** (default): hash-map based graph search. (Very memory hungry.)
- **`--dfs`**: plain depth-first search. (Much slower, but uses little memory.)
- **`--random[=NNN]`**: best of `NNN`many random playouts, defaulting to `100000`.
- **`--mcts[=NNN]`**: Monte Carlo Tree Search with random rollouts, defaulting to `500` simulations per real move.
- **`--full`**: An extended game where a list of trees is maintained and concatenation can be applied to selected trees.

### Command-line options

```text
tree-rotation [--verbose] [-o|--output FILE] [--start N] [--init MOVES] [--plot] [--full]
              [--dfs | --random | --random NNN | --mcts | --mcts NNN]
```

- `--verbose` prints improving leaders during the search; quiet mode is the default.
- `--output FILE` selects the CSV file to append to, or the CSV file to read when plotting.
- `--start N` chooses the first `N`; the defaults are `1` for the standard game and `3` with `--full`.
- `--init MOVES` starts the single-tree search from the position reached by applying the compact move string to the usual initial board; invalid or illegal prefixes are rejected.
- `--plot` reads the CSV file and prints an SVG plot of `N` versus high-score.
- `--full` analyses the multi-tree game.
- `--dfs`, `--random`, and `--mcts` choose alternative search strategies for the standard game.

### Build and run

This project is a Cabal package named `tree-rotation` and builds with the executable of the same name.

```bash
cabal build
cabal run tree-rotation -- --help
```

To locate the built executable directly:

```bash
cabal list-bin tree-rotation
```
