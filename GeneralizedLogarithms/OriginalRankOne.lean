import GeneralizedLogarithms.Foundations
import LogIrrationalityMeasure.Main

/-!
# Discharging the rank-one input

This bridge uses the original repository's main theorem to remove the
rank-one hypothesis from the nonvanishing reduction. It does not prove
the new higher-rank quantitative lower bound.
-/

namespace GeneralizedLogarithms

theorem original_rankOneLogarithmBounds : RankOneLogarithmBounds :=
  LogIrrationalityMeasure.LogExponent.log_eventualLowerBound

/-- Every nontrivial integer logarithmic linear form is nonzero, using the
original rank-one theorem and multiplicative independence. -/
theorem linearForm_ne_zero_unconditional
    {k : ℕ} (α : Fin k → ℚ) (hα : ∀ i, 0 < α i)
    (hind : MultiplicativelyIndependent α) (p : ℤ) (a : Fin k → ℤ)
    (hne : p ≠ 0 ∨ a ≠ 0) : linearForm α p a ≠ 0 :=
  linearForm_ne_zero original_rankOneLogarithmBounds α hα hind p a hne

end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.original_rankOneLogarithmBounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.original_rankOneLogarithmBounds

/-- info: 'GeneralizedLogarithms.linearForm_ne_zero_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.linearForm_ne_zero_unconditional
