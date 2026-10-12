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

The existing formalization was checked with Lean 4.34.1 during AI-assisted development. All 90 proof modules, the aggregate import, and the expanded statement passed. The guarded axiom reports for the main theorem and expanded statement contain exactly

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard axioms. The new sources contain no `sorry`, `admit`, custom axioms, `native_decide`, or `unsafe` declarations. The dependency's full build and its guarded axiom checks were also checked separately. These statements record the development checks; the commands below allow readers to reproduce verification from this repository.

## Build

With Git and the `elan` Lean toolchain manager installed, open a terminal in the repository directory and run:

```text
lake exe cache get
lake build
lake env lean Verification.lean
```

The project pins its toolchain and dependencies. On Windows, `$env:LEAN_NUM_THREADS = '1'` in PowerShell reduces Lean worker threads before running these commands. The first build also compiles the upstream formalization and may take substantially longer than later builds. [BUILDING.md](BUILDING.md) explains the commands and the expected output.

## Proof structure

1. Lower-rank bounds transfer through rational-subspace lattices. Failure of the desired bound then gives exceptional integer forms in general position, with sufficiently separated logarithmic weights.
2. Multilogarithmic jets, codimension-dependent multiplicity bounds, normal-space rigidity, and curve inequalities give geometric interpolation and nonzero rational minors.
3. Denominator clearing gives an arithmetic lower bound for those determinants.
4. Row translation and Taylor expansion give an analytic upper bound, using both small linear forms and collisions of transverse and Taylor modes.
5. A simultaneous parameter choice makes the two determinant bounds incompatible. Strong induction on $k$ proves the theorem.

The final assembly is in [`Main.lean`](GeneralizedLogarithms/Main.lean). The determinant contradiction is [`MultivariateDeterminantContradiction.impossible`](GeneralizedLogarithms/MultivariateDeterminantContradiction.lean), and the parameter existence theorem is [`MultivariateFixedParameters.exists_fixed`](GeneralizedLogarithms/MultivariateFixedParameters.lean).

## Dependencies and attribution

This project extends and imports [jdb19937/log-irrationality-measure](https://github.com/jdb19937/log-irrationality-measure), pinned to commit [`09aeeb095cebdce6791e24eff7f16d227edcdcb6`](https://github.com/jdb19937/log-irrationality-measure/tree/09aeeb095cebdce6791e24eff7f16d227edcdcb6), using its `lean` subdirectory. That repository's README describes its proof as a module-by-module modification of [OpenAI's formalization of the irrationality measure of pi](https://github.com/openai/math), under `lean/OAI/NumberTheory/PiExponent/`.

The toolchain is `leanprover/lean4:v4.34.1`. The upstream project pins [Mathlib](https://github.com/leanprover-community/mathlib4) to commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. The upstream sources remain an external dependency.
