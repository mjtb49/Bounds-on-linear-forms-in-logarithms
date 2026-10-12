import GeneralizedLogarithms.MultivariateRowTranslation

/-!
# The total-degree budget for multivariate logarithm tails

Each transverse tail is a sum over the longitudinal variables. Its order is
at least the fixed cutoff, regardless of the integer coefficients.
-/

namespace GeneralizedLogarithms.MultivariateTailBudget

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateRowTranslation

variable {k m : ℕ}

theorem order_tail (a : Fin m → Fin k → ℤ) (T : Fin m → ℕ) (i : Fin m) :
    (T i : ℕ∞) ≤ (tail a T i).order := by
  classical
  apply MvPowerSeries.nat_le_order
  intro d hd
  simp only [tail, map_sum, MvPowerSeries.coeff_C_mul]
  apply Finset.sum_eq_zero
  intro r hr
  by_cases he : d = Finsupp.single r (d r)
  · have hdeg : d.degree = d r := by conv_lhs => rw [he]; rw [Finsupp.degree_single]
    have hlt : d r < T i := hdeg ▸ hd
    simp only [PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.coeff_subst_single,
      ite_eq_left he, RowTranslation.coeff_tail_of_lt _ _ _ hlt, mul_zero]
  · simp only [PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.coeff_subst_single,
      ite_eq_right he, mul_zero]

theorem order_tail_product (a : Fin m → Fin k → ℤ) (T d : Fin m → ℕ) :
    ((∑ i, d i * T i : ℕ) : ℕ∞) ≤ (∏ i, tail a T i ^ d i).order := by
  calc
    _ = ∑ i, d i • (T i : ℕ∞) := by simp [nsmul_eq_mul]
    _ ≤ ∑ i, d i • (tail a T i).order :=
      Finset.sum_le_sum (fun i _ => nsmul_le_nsmul_right (order_tail a T i) _)
    _ ≤ ∑ i, (tail a T i ^ d i).order :=
      Finset.sum_le_sum (fun i _ => MvPowerSeries.le_order_pow (d i))
    _ ≤ _ := MvPowerSeries.le_order_prod _ _

theorem tail_budget_nat (a : Fin m → Fin k → ℤ) (T d : Fin m → ℕ) (s : Fin k →₀ ℕ)
    (hne : MvPowerSeries.coeff s (∏ i, tail a T i ^ d i) ≠ 0) :
    ∑ i, d i * T i ≤ s.degree := by
  exact_mod_cast (order_tail_product a T d).trans (MvPowerSeries.order_le hne)

theorem tail_weight_budget (a : Fin m → Fin k → ℤ) (T d : Fin m → ℕ) (s : Fin k →₀ ℕ)
    (w : Fin m → ℝ) (v₀ F : ℝ) (hv₀ : 0 ≤ v₀) (hF : 0 < F)
    (hT : ∀ i, F * w i ≤ v₀ * T i)
    (hne : MvPowerSeries.coeff s (∏ i, tail a T i ^ d i) ≠ 0) :
    ∑ i, (d i : ℝ) * w i ≤ v₀ * s.degree / F := by
  apply (le_div_iff₀ hF).mpr
  calc
    _ = ∑ i, (d i : ℝ) * (F * w i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, (d i : ℝ) * (v₀ * T i) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hT i) (Nat.cast_nonneg _)
    _ = v₀ * ((∑ i, d i * T i : ℕ) : ℝ) := by
      simp only [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast tail_budget_nat a T d s hne) hv₀

end
end GeneralizedLogarithms.MultivariateTailBudget

/-- info: 'GeneralizedLogarithms.MultivariateTailBudget.tail_weight_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateTailBudget.tail_weight_budget
