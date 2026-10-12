# Building and reading the theorem

This walkthrough compiles the Lean project, checks the expanded theorem statement, and explains how its notation corresponds to the mathematical claim in the README.

## Open the local repository

You need Git and the `elan` Lean toolchain manager. If they are already installed, use a terminal to check that the commands are available:

```text
git --version
elan --version
```

If you already have the repository folder locally, open a terminal inside `bounds-on-linear-forms-in-logarithms` and skip the clone command. The directory should contain `lakefile.toml` and `lean-toolchain`.

After the repository is published on GitHub, a new checkout can be obtained with the following commands, replacing `YOUR-USERNAME` with its GitHub owner:

```text
git clone https://github.com/YOUR-USERNAME/bounds-on-linear-forms-in-logarithms.git
cd bounds-on-linear-forms-in-logarithms
```

Keep the terminal in this directory for the remaining commands. `lean-toolchain` selects Lean 4.34.1; `elan` obtains that toolchain when needed.

## Compile the project

On Windows, first run this in PowerShell to reduce Lean worker threads:

```powershell
$env:LEAN_NUM_THREADS = '1'
```

Then run these commands one at a time, waiting for each to finish successfully:

```text
lake exe cache get
lake build
lake env lean Verification.lean
```

`lake exe cache get` downloads precompiled Mathlib dependencies. It needs an internet connection. `lake build` compiles this project's two default targets: the aggregate `GeneralizedLogarithms` library, which imports all 90 proof modules, and `Verification`. It also builds the imported upstream formalization. The first build can take a while; later builds reuse completed work.

`lake env lean Verification.lean` explicitly checks the expanded statement again and prints its type and axiom dependencies. Successful output includes:

```text
'GeneralizedLogarithms.Verification.exact_statement' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

Line wrapping may differ. Each command should exit successfully. A warning is distinct from an error; a failed build or failed `#guard_msgs` check requires investigation. In PowerShell, `$LASTEXITCODE` immediately after a command is `0` for success.

The `#guard_msgs` blocks compare Lean's actual axiom report with the expected report. The text in their preceding comments is not itself evidence of success: Lean must run and accept the guard.

## Find the main statement

Open [`GeneralizedLogarithms/Main.lean`](GeneralizedLogarithms/Main.lean) and find `theorem logarithmic_linear_forms` near the end. Its full name is `GeneralizedLogarithms.logarithmic_linear_forms` because it is declared inside that namespace.

```lean
theorem logarithmic_linear_forms {k : ℕ} (α : Fin k → ℚ)
    (hα : ∀ r, 0 < α r) (hind : MultiplicativelyIndependent α) :
    ∀ ν : ℝ, (k : ℝ) < ν → ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ),
      H₀ ≤ coefficientHeight p a →
        (coefficientHeight p a : ℝ)^(-ν) ≤
          |(p : ℝ)+∑ r, (a r : ℝ)*Real.log (α r)| :=
  eventualLowerBound_all k α hα hind
```

Read everything before `:=` as the theorem statement. The expression after it is the proof, using `eventualLowerBound_all`, proved immediately above it.

| Lean expression | Mathematical meaning |
| --- | --- |
| `ℕ`, `ℤ`, `ℚ`, `ℝ` | Natural numbers, integers, rationals, and reals |
| `{k : ℕ}` | The rank is an implicit natural-number parameter |
| `Fin k` | The finite index set `0, …, k − 1` |
| `α : Fin k → ℚ` | A family of `k` rational numbers |
| `hα : ∀ r, 0 < α r` | Every member of the family is positive |
| `hind : MultiplicativelyIndependent α` | The family has no nontrivial integer multiplicative relation |
| `∀ ν : ℝ, (k : ℝ) < ν →` | For every real exponent greater than the rank |
| `∃ H₀ : ℕ` | There exists a natural-number threshold |
| `∀ (p : ℤ) (a : Fin k → ℤ)` | For every integer constant and every family of integer coefficients |
| `H₀ ≤ coefficientHeight p a →` | Provided the coefficient height is at least that threshold |
| `(coefficientHeight p a : ℝ)^(-ν)` | The real power $H^{-\nu}$ |
| `∑ r, (a r : ℝ)*Real.log (α r)` | The sum $\sum_r a_r\log\alpha_r$ |

`∀` means “for every,” `∃` means “there exists,” and `→` means “implies.” Expressions such as `(p : ℝ)` embed an integer into the real numbers. These casts do not change its numerical value. `Real.log` is the natural logarithm.

The order of the quantifiers matters: $H_0$ may depend on the rational family and on $\nu$, but it is chosen before $p$ and $a$. The theorem provides one threshold that works for all sufficiently large coefficient tuples. It gives no formula for that threshold.

## Expand the two definitions

[`GeneralizedLogarithms/Foundations.lean`](GeneralizedLogarithms/Foundations.lean) defines the height as

```lean
def coefficientHeight {k : ℕ} (p : ℤ) (a : Fin k → ℤ) : ℕ :=
  max 2 (max p.natAbs (Finset.univ.sup fun i => (a i).natAbs))
```

`natAbs` is an integer's absolute value as a natural number. `Finset.univ.sup` takes the maximum over the finite index set. Thus the definition is exactly $\max(2,|p|,|a_1|,\ldots,|a_k|)$, with Lean indexing the coefficients from zero.

The same file defines independence as

```lean
def MultiplicativelyIndependent {k : ℕ} (α : Fin k → ℚ) : Prop :=
  ∀ a : Fin k → ℤ, (∏ i, α i ^ a i) = 1 → a = 0
```

Here `∏` is a finite product and `a = 0` means that every coefficient is zero. Because the exponents are integers, relations involving quotients are included.

[`Verification.lean`](Verification.lean) puts both definitions directly into `exact_statement`. That theorem is derived from the main theorem; it is an independently written presentation of the statement, not a second mathematical proof. Comparing it with the README is a useful way to check that Lean has proved the intended claim.
