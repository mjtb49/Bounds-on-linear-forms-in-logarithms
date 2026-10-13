# Building and checking the theorem

Use Linux (including Ubuntu in WSL2), with Git, [elan](https://github.com/leanprover/elan), and Bubblewrap installed. On Ubuntu, install Bubblewrap with `sudo apt install bubblewrap`. The repository selects Lean 4.35.0 through `lean-toolchain`; elan obtains that version when needed.

## Prepare a fresh checkout

Run these commands from a Linux terminal, checking that each succeeds:

```bash
git clone https://github.com/mjtb49/Bounds-on-linear-forms-in-logarithms.git
cd Bounds-on-linear-forms-in-logarithms

mkdir -p .lake/packages
git clone --no-checkout https://github.com/jdb19937/log-irrationality-measure.git \
  .lake/packages/log-irrationality-measure
git -C .lake/packages/log-irrationality-measure checkout --detach \
  09aeeb095cebdce6791e24eff7f16d227edcdcb6
git -C .lake/packages/log-irrationality-measure apply \
  "$PWD/patches/log-dependency-435.patch"
```

The committed patch adapts the pinned upstream sources to Lean 4.35. Apply it once per fresh dependency checkout. All remaining dependency revisions are fixed by `lake-manifest.json`; no `lake update` is needed.

## Run comparator

From the repository root:

```bash
lake comparator --paranoid
echo $?
```

This runs Lean's official comparator with its default sandbox and all bundled external checkers. It downloads the remaining pinned dependencies, builds the challenge and solution, and checks the exported proof. The first build compiles dependencies from source and can take substantial time. Subsequent runs reuse completed work in `.lake`; rerun the comparator command without repeating the patch step.

A successful run reports acceptance from each of these kernels:

- Lean paranoid
- lean4lean
- nanoda
- con-leche
- con-ron
- Lean default

It then prints `Your solution is okay!` and exits with code `0`. A successful build alone is not comparator acceptance. Inspect the raw output if any step fails.

## Read the statement

Open [`Challenge.lean`](Challenge.lean), which imports only Mathlib and states `rational_logarithmic_linear_forms` with the mathematical definitions expanded. Its `by sorry` is the intentional challenge placeholder; the corresponding build warning is expected.

[`Solution.lean`](Solution.lean) proves the same statement using [`GeneralizedLogarithms/Main.lean`](GeneralizedLogarithms/Main.lean), without importing the challenge. [`comparator.json`](comparator.json) permits only `propext`, `Quot.sound`, and `Classical.choice`.

The height in the statement is `max 2 (max p.natAbs (Finset.univ.sup fun i => (a i).natAbs))`, meaning $\max(2,|p|,|a_1|,\ldots,|a_k|)$. The independence hypothesis says that an integer multiplicative relation among the rational arguments must have all exponents zero. The threshold is chosen after the rational family and the exponent, but before the integer coefficients.

For editor use, open the repository in VS Code with the Lean extension. On Windows, open the Linux checkout using VS Code's WSL integration. After comparator finishes building, use Lean's **Restart File** command if an already-open file reports outdated imports.
