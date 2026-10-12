import GeneralizedLogarithms.Main

open scoped BigOperators

namespace GeneralizedLogarithms.Verification

/-- Independent restatement with the height and independence condition expanded. -/
theorem exact_statement (k : ℕ) (α : Fin k → ℚ)
    (hpositive : ∀ i, 0 < α i)
    (hindependent : ∀ b : Fin k → ℤ, (∏ i, α i ^ b i) = 1 → b = 0) :
    ∀ ν : ℝ, (k : ℝ) < ν → ∃ H₀ : ℕ,
      ∀ (p : ℤ) (a : Fin k → ℤ),
        H₀ ≤ max 2 (max p.natAbs (Finset.univ.sup fun i => (a i).natAbs)) →
        ((max 2 (max p.natAbs (Finset.univ.sup fun i => (a i).natAbs)) : ℕ) : ℝ)^(-ν) ≤
          |(p : ℝ)+∑ i, (a i : ℝ)*Real.log (α i)| :=
  logarithmic_linear_forms α hpositive hindependent

/-- info: 'GeneralizedLogarithms.Verification.exact_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_statement

#check exact_statement
#print axioms exact_statement

end GeneralizedLogarithms.Verification
