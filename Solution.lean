import GeneralizedLogarithms.Main

/-!
Solution for comparator. The statement is repeated independently of Challenge;
the proof uses the main theorem. Do not import Challenge here.
-/

open scoped BigOperators

theorem rational_logarithmic_linear_forms
    (k : ℕ) (α : Fin k → ℚ)
    (hpositive : ∀ i, 0 < α i)
    (hindependent :
      ∀ b : Fin k → ℤ, (∏ i, α i ^ b i) = 1 → b = 0) :
    ∀ ν : ℝ, (k : ℝ) < ν → ∃ H₀ : ℕ,
      ∀ (p : ℤ) (a : Fin k → ℤ),
        H₀ ≤ max 2 (max p.natAbs (Finset.univ.sup fun i => (a i).natAbs)) →
        ((max 2 (max p.natAbs (Finset.univ.sup fun i => (a i).natAbs)) : ℕ) : ℝ) ^ (-ν) ≤
          |(p : ℝ) + ∑ i, (a i : ℝ) * Real.log (α i : ℝ)| := by
  exact GeneralizedLogarithms.logarithmic_linear_forms α hpositive hindependent

/-- info: 'rational_logarithmic_linear_forms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rational_logarithmic_linear_forms
