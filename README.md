# Bounds on linear forms in logarithms

A Lean formalization of an eventual lower bound for integer linear forms in logarithms of positive rational numbers, with an integer constant term.

For every finite multiplicatively independent family of positive rationals $\alpha_1,\ldots,\alpha_k$ and every real $\nu>k$, there exists $H_0\in\mathbb N$ such that all integers $p,a_1,\ldots,a_k$ with

$$H=\max(2,|p|,|a_1|,\ldots,|a_k|)\ge H_0$$

satisfy

$$\left|p+\sum_{i=1}^{k}a_i\log\alpha_i\right|\ge H^{-\nu}.$$

The logarithm is the real natural logarithm. Multiplicative independence means that $\prod_i\alpha_i^{b_i}=1$ for integers $b_i$ implies every $b_i=0$. The theorem applies to every rank $k$; it does not give an explicit value for $H_0$.

The main declaration is [`GeneralizedLogarithms.logarithmic_linear_forms`](GeneralizedLogarithms/Main.lean). [`Verification.lean`](Verification.lean) restates it with the height and independence definitions expanded. See [the build and reading walkthrough](BUILDING.md) to compile the project and inspect the statement.

# Note from the human
This proof arose out of my attempt at understanding OpenAI's recent improvements to the irrationality measure of $\pi$ and the subsequent generalization to irrationality measures of logarithms of rational numbers. My input was minimal, I simply asked ChatGPT 5.6 why multiple exponentials in the matrix would not prove a strong bound on linear forms in logarithms, and it spat out this proof. I have yet to go through the main statement of the repository too carefully, nor have I confirmed the fact that the lean builds independently. This disclaimer will be updated when I have done so. On the other hand, I have read closely and think I understand the proof, and perhaps will try and write a human understandable explanation if there is interest. 

## Verification status

On 2026-10-13, the maintainer ran the official `lake comparator --paranoid` with Lean 4.35.0 on Linux. The build completed successfully, and all six kernel checks accepted the solution: Lean paranoid, lean4lean, nanoda, con-leche, con-ron, and Lean default. Comparator finished with `Your solution is okay!`. The [saved transcript excerpt](verification/comparator-output.txt) records the final build and checking output supplied by the maintainer.

[`Challenge.lean`](Challenge.lean) imports only Mathlib and states `rational_logarithmic_linear_forms` with the height and independence definitions expanded. Its `by sorry` is the intentional challenge placeholder. [`Solution.lean`](Solution.lean) independently repeats that statement and proves it from the main theorem, without importing the challenge. [`comparator.json`](comparator.json) permits only `propext`, `Quot.sound`, and `Classical.choice`.

The committed Lean sources match the source snapshot from that successful run. The toolchain, dependency revisions, and [upstream compatibility patch](patches/log-dependency-435.patch) reproduce its proof inputs. Verification checks the formal statement; readers should inspect `Challenge.lean` to confirm that it expresses the mathematical claim above.

## Build and verify

Follow [BUILDING.md](BUILDING.md) to prepare a fresh checkout, apply the upstream patch, and run the official comparator with its default sandbox and external checkers. The first build compiles the pinned dependencies from source; subsequent runs reuse completed work.

## Proof structure

1. Lower-rank bounds transfer through rational-subspace lattices. Failure of the desired bound then gives exceptional integer forms in general position, with sufficiently separated logarithmic weights.
2. Multilogarithmic jets, codimension-dependent multiplicity bounds, normal-space rigidity, and curve inequalities give geometric interpolation and nonzero rational minors.
3. Denominator clearing gives an arithmetic lower bound for those determinants.
4. Row translation and Taylor expansion give an analytic upper bound, using both small linear forms and collisions of transverse and Taylor modes.
5. A simultaneous parameter choice makes the two determinant bounds incompatible. Strong induction on $k$ proves the theorem.

The final assembly is in [`Main.lean`](GeneralizedLogarithms/Main.lean). The determinant contradiction is [`MultivariateDeterminantContradiction.impossible`](GeneralizedLogarithms/MultivariateDeterminantContradiction.lean), and the parameter existence theorem is [`MultivariateFixedParameters.exists_fixed`](GeneralizedLogarithms/MultivariateFixedParameters.lean).

## Dependencies and attribution

This project extends and imports [jdb19937/log-irrationality-measure](https://github.com/jdb19937/log-irrationality-measure), pinned to commit [`09aeeb095cebdce6791e24eff7f16d227edcdcb6`](https://github.com/jdb19937/log-irrationality-measure/tree/09aeeb095cebdce6791e24eff7f16d227edcdcb6), using its `lean` subdirectory. That repository's README describes its proof as a module-by-module modification of [OpenAI's formalization of the irrationality measure of pi](https://github.com/openai/math), under `lean/OAI/NumberTheory/PiExponent/`.

The toolchain is `leanprover/lean4:v4.35.0`. This project pins [Mathlib](https://github.com/leanprover-community/mathlib4) to commit `fad34067088f101a9a302d9393aacbffa190694c`; all dependency revisions are recorded in `lake-manifest.json`. The upstream logarithm formalization remains an external dependency, with a committed compatibility patch for two valuation API changes, a redundant tactic, and multiline singleton syntax. The patch does not change the mathematical statements.
