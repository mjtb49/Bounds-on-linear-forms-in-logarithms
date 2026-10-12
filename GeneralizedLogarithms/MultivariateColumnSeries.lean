import GeneralizedLogarithms.MultivariateRowTranslation
import GeneralizedLogarithms.MultivariateTensorCoefficients
import GeneralizedLogarithms.MultivariateColumnGrowth
import GeneralizedLogarithms.MultivariateCauchyCoefficient

/-!
# Taylor coefficients of the actual translated columns

The coefficient depends on the transverse multi-index and the column, but
not on the jet center or derivative row. This is the grouping required by
the proved determinant collision bound.
-/

namespace GeneralizedLogarithms.MultivariateColumnSeries

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateAnalyticSeries MultivariateTensorCoefficients MultivariateRowTranslation

variable {k m : ℕ}

def transversePolynomial (a : Fin m → Fin k → ℤ) (b γ : Fin m →₀ ℕ) : MvPolynomial (Fin k) ℂ :=
  MvPolynomial.C ((∏ i, (b i).choose (γ i) : ℕ) : ℂ) *
    ∏ i, (∑ r, MvPolynomial.C (a i r : ℂ) * MvPolynomial.X r) ^ (b i - γ i)

theorem aeval_transversePolynomial {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : Fin m → Fin k → ℤ) (b γ : Fin m →₀ ℕ) (z : Fin k → A) :
    MvPolynomial.aeval z (transversePolynomial a b γ) =
      algebraMap ℂ A ((∏ i, (b i).choose (γ i) : ℕ) : ℂ) *
        ∏ i, (∑ r, algebraMap ℂ A (a i r : ℂ) * z r) ^ (b i - γ i) := by
  simp only [transversePolynomial, map_mul, map_prod, map_pow, map_sum,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]

theorem periodMonomial_coeff (y ω : Fin k → ℂ) (a : Fin m → Fin k → ℤ) (j : ℕ)
    (h : Fin k →₀ ℕ) (b γ : Fin m →₀ ℕ) :
    (periodMonomial y ω a j h b).coeff γ =
      formalPolynomialRow (transversePolynomial a b γ) h ω y j := by
  have hs : periodMonomial y ω a j h b = MvPolynomial.C (exponentialFactor y j h) *
      RowTranslation.shift (periodCoordinate a ω j) (MvPolynomial.monomial b 1) := by
    simp only [periodMonomial, exponentialFactor, RowTranslation.shift_monomial_one]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [add_comm]
  rw [hs, MvPolynomial.coeff_C_mul]
  change exponentialFactor y j h * RowTranslation.shiftCoefficient (periodCoordinate a ω j) γ b = _
  rw [RowTranslation.shiftCoefficient_eq, Finset.prod_mul_distrib, formalPolynomialRow,
    aeval_transversePolynomial]
  simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    map_natCast, Nat.cast_prod, periodCoordinate, periodVector]
  simp only [map_prod, map_natCast, mul_assoc]

theorem hasSum_actual_period_coefficient (y ω : Fin k → ℂ) (a : Fin m → Fin k → ℤ)
    (hy : ∀ r, Complex.exp (ω r) = y r) (j : ℕ) (h : Fin k →₀ ℕ) (b γ : Fin m →₀ ℕ)
    (R : NNReal) (hR : 0 < R)
    (hc : ∀ r, ‖(j : ℂ) * ω r‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : Fin k →₀ ℕ) :
    HasSum (fun d => rowTestTensor (fun r => (j : ℂ) * ω r) R ell d *
      polynomialTaylor (transversePolynomial a b γ) h R d)
      (MvPowerSeries.coeff ell ((periodMonomial y ω a j h b).coeff γ)) := by
  rw [periodMonomial_coeff]
  exact hasSum_formalPolynomialRow _ h ω y hy j R hR hc ell

theorem exponentialPolynomial_eq_columnFunction (a : Fin m → Fin k → ℤ)
    (h : Fin k → ℕ) (b γ : Fin m →₀ ℕ) (z : Fin k → ℂ) :
    MultivariateCauchyCoefficient.exponentialPolynomial (transversePolynomial a b γ) h z =
      MultivariateColumnGrowth.columnFunction a h b γ z := by
  simp only [MultivariateCauchyCoefficient.exponentialPolynomial, transversePolynomial,
    map_mul, map_prod, map_sum, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
    MultivariateColumnGrowth.columnFunction]
  ring

theorem norm_actual_taylor_coefficient (hk : 0 < k)
    (a : Fin m → Fin k → ℤ) (h : Fin k → ℕ) (b γ : Fin m →₀ ℕ) (w : Fin m → ℝ)
    (H R w₀ wstar : ℝ) (hH : 0 ≤ H) (hR : 1 ≤ R) (hw₀ : 0 < w₀) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hγ : γ ≤ b)
    (hcol : w₀ * (∑ r, (h r : ℝ)) + ∑ i, w i * b i ≤ H)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i)) (d : Fin k → ℕ) :
    ‖polynomialTaylor (transversePolynomial a b γ) h R d‖ ≤
      Real.exp (H - (∑ i, w i * γ i) + H * (R / w₀ + Real.log (2 * k * R) / wstar)) := by
  apply MultivariateCauchyCoefficient.norm_polynomialTaylor_le _ h R _ (zero_lt_one.trans_le hR)
  intro z hz
  rw [exponentialPolynomial_eq_columnFunction]
  exact MultivariateColumnGrowth.norm_columnFunction_exp_budget hk a h b γ w H R w₀ wstar
    hH hR hw₀ hws hw hγ hcol ha z (fun r => (hz r).le)

theorem transversePolynomial_eq_zero_of_not_le (a : Fin m → Fin k → ℤ)
    (b γ : Fin m →₀ ℕ) (hne : ¬ γ ≤ b) : transversePolynomial a b γ = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, b i < γ i := by simpa only [Finsupp.le_def, not_forall, not_le] using hne
  have hz : (∏ i, (b i).choose (γ i) : ℕ) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (Nat.choose_eq_zero_of_lt hi)
  simp [transversePolynomial, hz]

theorem norm_actual_taylor_coefficient_all (hk : 0 < k)
    (a : Fin m → Fin k → ℤ) (h : Fin k → ℕ) (b γ : Fin m →₀ ℕ) (w : Fin m → ℝ)
    (H R w₀ wstar : ℝ) (hH : 0 ≤ H) (hR : 1 ≤ R) (hw₀ : 0 < w₀) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w₀ * (∑ r, (h r : ℝ)) + ∑ i, w i * b i ≤ H)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i)) (d : Fin k → ℕ) :
    ‖polynomialTaylor (transversePolynomial a b γ) h R d‖ ≤
      Real.exp (H - (∑ i, w i * γ i) + H * (R / w₀ + Real.log (2 * k * R) / wstar)) := by
  by_cases hγ : γ ≤ b
  · exact norm_actual_taylor_coefficient hk a h b γ w H R w₀ wstar hH hR hw₀ hws hw hγ hcol ha d
  · rw [transversePolynomial_eq_zero_of_not_le a b γ hγ]
    simp [polynomialTaylor, Real.exp_nonneg]

def normalizedCoefficient (a : Fin m → Fin k → ℤ) (h : Fin k → ℕ) (b γ : Fin m →₀ ℕ)
    (w : Fin m → ℝ) (R : ℝ) (d : Fin k → ℕ) : ℂ :=
  (Real.exp (∑ i, w i * γ i) : ℂ) * polynomialTaylor (transversePolynomial a b γ) h R d

theorem norm_normalizedCoefficient_le (hk : 0 < k)
    (a : Fin m → Fin k → ℤ) (h : Fin k → ℕ) (b γ : Fin m →₀ ℕ) (w : Fin m → ℝ)
    (H R w₀ wstar : ℝ) (hH : 0 ≤ H) (hR : 1 ≤ R) (hw₀ : 0 < w₀) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i)
    (hcol : w₀ * (∑ r, (h r : ℝ)) + ∑ i, w i * b i ≤ H)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i)) (d : Fin k → ℕ) :
    ‖normalizedCoefficient a h b γ w R d‖ ≤
      Real.exp (H * (1 + R / w₀ + Real.log (2 * k * R) / wstar)) := by
  rw [normalizedCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (∑ i, w i * γ i) *
        Real.exp (H - (∑ i, w i * γ i) + H * (R / w₀ + Real.log (2 * k * R) / wstar)) :=
      mul_le_mul_of_nonneg_left
        (norm_actual_taylor_coefficient_all hk a h b γ w H R w₀ wstar hH hR hw₀ hws hw hcol ha d)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end
end GeneralizedLogarithms.MultivariateColumnSeries

/-- info: 'GeneralizedLogarithms.MultivariateColumnSeries.hasSum_actual_period_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateColumnSeries.hasSum_actual_period_coefficient

/-- info: 'GeneralizedLogarithms.MultivariateColumnSeries.norm_actual_taylor_coefficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateColumnSeries.norm_actual_taylor_coefficient
