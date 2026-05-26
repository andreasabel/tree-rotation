# tree-rotation

Tools for exploring the tree-rotation puzzle from <https://github.com/koengit/puzzle2026>.

This repository contains two main components:

1. A browser playground for interactively stepping through move strings and visualizing the current tree.
2. A Haskell program, `tree-rotation`, for exact and approximate high-score search, CSV output, and SVG plotting.

The project is licensed under the **BSD 3-clause license**; see [LICENSE](LICENSE).

## Web playground

The interactive page lives at [play/index.html](play/index.html).

It is a self-contained visualization of the reduced tree game. The page shows:

- the current counts of `C`, `T`, and `R` moves and the ratio `R/C`,
- an SVG rendering of the current tree, omitting `Leaf` nodes,
- a move-input field that drives the whole display.

### How to play

Open `play/index.html` in a browser, then type a move string such as `ccrtt` into the input field.

- `c` appends a `Leaf` on the right, consuming one available concatenation move,
- `r` performs a tree rotation when the current tree has the right shape,
- `t` takes the tail when the current tree has the form `Node Leaf t`.

The page evaluates only the prefix up to the current cursor position, so you can move the caret backward and forward through a longer sequence and inspect intermediate states without deleting text. If the prefix is illegal, the tree pane shows a large red `X` and the statistics are marked invalid as well.

## Haskell program

The command-line solver is the executable **`tree-rotation`**.

By default it solves the reduced game, starting at `N = 1`, and keeps running for `N, N+1, N+2, ...` until interrupted. For each solved `N`, it prints the final winner and appends a CSV row with

```text
n,score,ratio,iterations,moves
```

where `score` is the number of rotations, `ratio` is `score / n`, `iterations` is the search-specific work counter, and `moves` is the winning move trail.

### Search modes

- **Exact search** (default): hash-map based graph search for the reduced game.
- **`--dfs`**: plain depth-first search for the reduced game.
- **`--random[=NNN]`**: best of many random playouts, defaulting to `100000`.
- **`--mcts[=NNN]`**: Monte Carlo Tree Search with random rollouts, defaulting to `100000` simulations per real move.
- **`--full`**: switch to the original indexed multi-tree game instead of the reduced game.

### Command-line options

```text
tree-rotation [--verbose] [-o|--output FILE] [--start N] [--plot] [--full]
              [--dfs | --random | --random NNN | --mcts | --mcts NNN]
```

- `--verbose` prints improving leaders during the search; quiet mode is the default.
- `--output FILE` selects the CSV file to append to, or the CSV file to read when plotting.
- `--start N` chooses the first `N`; the defaults are `1` for the reduced game and `3` with `--full`.
- `--plot` reads the CSV file and prints an SVG plot of `N` versus high-score.
- `--full` uses the original board-of-trees game with indexed moves.
- `--dfs`, `--random`, and `--mcts` choose alternative search strategies for the reduced game.

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

The code is written in **GHC2021** and currently depends on:

- `base`
- `directory`
- `hashable`
- `optparse-applicative`
- `random`
- `unordered-containers`
