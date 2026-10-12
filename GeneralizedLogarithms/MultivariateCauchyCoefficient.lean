import GeneralizedLogarithms.MultivariateAnalyticSeries
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Cauchy bounds for the tensor Taylor coefficients

The finite product of one-dimensional contour kernels realizes the previously
constructed tensor coefficient as one integral over the product of circles.
-/

namespace GeneralizedLogarithms.MultivariateCauchyCoefficient

noncomputable section
open scoped BigOperators
open MeasureTheory Set
open LogIrrationalityMeasure.LogExponent.AnalyticCollision
open MultivariateAnalyticSeries

def angleMeasure (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ => (volume : Measure ℝ).restrict (Icc 0 (2 * Real.pi)))

instance (k : ℕ) : IsFiniteMeasure (angleMeasure k) := by
  unfold angleMeasure
  infer_instance

def kernel (R : ℝ) (d : ℕ) (θ : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * deriv (circleMap 0 R) θ *
    ((R : ℂ) / circleMap 0 R θ) ^ d * (circleMap 0 R θ)⁻¹

theorem normalizedTaylorCoeff_integral (f : ℂ → ℂ) (R : ℝ) (d : ℕ) :
    normalizedTaylorCoeff f R d =
      ∫ θ, kernel R d θ * f (circleMap 0 R θ)
        ∂((volume : Measure ℝ).restrict (Icc 0 (2 * Real.pi))) := by
  rw [normalizedTaylorCoeff, cauchyPowerSeries_apply, circleIntegral_def_Icc]
  simp only [sub_zero, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by simp only [kernel]; ring

theorem circle_ne_zero (R : ℝ) (hR : 0 < R) (θ : ℝ) : circleMap 0 R θ ≠ 0 := by
  apply norm_pos_iff.mp
  simpa only [norm_circleMap_zero, abs_of_pos hR] using hR

theorem norm_kernel (R : ℝ) (hR : 0 < R) (d : ℕ) (θ : ℝ) :
    ‖kernel R d θ‖ = (2 * Real.pi)⁻¹ := by
  simp only [kernel, norm_mul, norm_inv, norm_pow, norm_div,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    abs_of_pos Real.pi_pos, mul_one, deriv_circleMap, norm_circleMap_zero,
    abs_of_pos hR]
  simp [norm_mul, norm_circleMap_zero, abs_of_pos hR, hR.ne']

theorem continuous_kernel (R : ℝ) (hR : 0 < R) (d : ℕ) : Continuous (kernel R d) := by
  unfold kernel
  simp only [deriv_circleMap]
  have hc : Continuous (circleMap 0 R) := by fun_prop
  exact ((continuous_const.mul (hc.mul continuous_const)).mul
    ((continuous_const.div₀ hc (circle_ne_zero R hR)).pow d)).mul
    (hc.inv₀ (circle_ne_zero R hR))

theorem integrable_kernel_mul (f : ℂ → ℂ) (hf : Continuous f) (R : ℝ) (hR : 0 < R) (d : ℕ) :
    Integrable (fun θ => kernel R d θ * f (circleMap 0 R θ))
      ((volume : Measure ℝ).restrict (Icc 0 (2 * Real.pi))) := by
  exact ((continuous_kernel R hR d).mul (hf.comp (by fun_prop))).integrableOn_Icc

def coefficient {k : ℕ} (f : (Fin k → ℂ) → ℂ) (R : ℝ) (d : Fin k → ℕ) : ℂ :=
  ∫ θ, (∏ r, kernel R (d r) (θ r)) * f (fun r => circleMap 0 R (θ r)) ∂angleMeasure k

theorem coefficient_product {k : ℕ} (f : Fin k → ℂ → ℂ) (R : ℝ) (d : Fin k → ℕ) :
    coefficient (fun z => ∏ r, f r (z r)) R d = taylorTensor f R d := by
  unfold coefficient angleMeasure taylorTensor
  simp only [← Finset.prod_mul_distrib]
  calc
    _ = ∏ r, ∫ θ, kernel R (d r) θ * f r (circleMap 0 R θ)
        ∂((volume : Measure ℝ).restrict (Icc 0 (2 * Real.pi))) :=
      integral_fintype_prod_eq_prod (fun r θ => kernel R (d r) θ * f r (circleMap 0 R θ))
    _ = _ := by simp only [← normalizedTaylorCoeff_integral]

theorem mass_angleMeasure (k : ℕ) : (angleMeasure k).real univ = (2 * Real.pi) ^ k := by
  simp [measureReal_def, angleMeasure, Measure.pi_univ, Real.volume_Icc, Real.two_pi_pos.le,
    Real.pi_pos.le]

theorem norm_coefficient_le {k : ℕ} (f : (Fin k → ℂ) → ℂ) (R D : ℝ) (hR : 0 < R)
    (hf : ∀ z, (∀ r, ‖z r‖ = R) → ‖f z‖ ≤ D) (d : Fin k → ℕ) :
    ‖coefficient f R d‖ ≤ D := by
  have hb (θ : Fin k → ℝ) :
      ‖(∏ r, kernel R (d r) (θ r)) * f (fun r => circleMap 0 R (θ r))‖ ≤
        ((2 * Real.pi)⁻¹) ^ k * D := by
    rw [norm_mul, norm_prod]
    simp only [norm_kernel R hR, Fin.prod_const]
    exact mul_le_mul_of_nonneg_left (hf _ (fun r => by simp [norm_circleMap_zero, abs_of_pos hR]))
      (by positivity)
  have hh := norm_integral_le_of_norm_le_const (μ := angleMeasure k) (Filter.Eventually.of_forall hb)
  rw [mass_angleMeasure] at hh
  unfold coefficient
  convert hh using 1
  rw [inv_pow]
  field_simp

def exponentialPolynomial {k : ℕ} (P : MvPolynomial (Fin k) ℂ) (h : Fin k → ℕ)
    (z : Fin k → ℂ) : ℂ := Complex.exp (∑ r, (h r : ℂ) * z r) * MvPolynomial.eval z P

theorem exponentialPolynomial_expansion {k : ℕ} (P : MvPolynomial (Fin k) ℂ)
    (h : Fin k → ℕ) (z : Fin k → ℂ) :
    exponentialPolynomial P h z =
      ∑ e ∈ P.support, P.coeff e * ∏ r, exponentialFactors h e r (z r) := by
  classical
  rw [exponentialPolynomial, MvPolynomial.eval_eq']
  simp only [RingHom.id_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [exponentialFactors, LogIrrationalityMeasure.LogExponent.AnalyticCollision.exponentialMonomial,
    one_mul, Finset.prod_mul_distrib, ← Complex.exp_sum]
  ring

theorem coefficient_exponentialPolynomial {k : ℕ} (P : MvPolynomial (Fin k) ℂ)
    (h : Fin k → ℕ) (R : ℝ) (hR : 0 < R) (d : Fin k → ℕ) :
    coefficient (exponentialPolynomial P h) R d = polynomialTaylor P h R d := by
  classical
  simp only [coefficient, exponentialPolynomial_expansion, Finset.mul_sum]
  rw [integral_finset_sum]
  · rw [polynomialTaylor]
    apply Finset.sum_congr rfl
    intro e he
    rw [show (fun θ : Fin k → ℝ => (∏ r, kernel R (d r) (θ r)) *
        (P.coeff e * ∏ r, exponentialFactors h e r (circleMap 0 R (θ r)))) =
        fun θ => P.coeff e * ((∏ r, kernel R (d r) (θ r)) *
          ∏ r, exponentialFactors h e r (circleMap 0 R (θ r))) by funext θ; ring,
      integral_const_mul]
    exact congrArg (P.coeff e * ·) (coefficient_product (exponentialFactors h e) R d)
  · intro e he
    have hi := Integrable.fintype_prod (fun r => integrable_kernel_mul (exponentialFactors h e r)
      (differentiable_exponentialMonomial _ _ _).continuous R hR (d r))
    have hh := hi.const_mul (P.coeff e)
    change Integrable _ (Measure.pi (fun _ : Fin k => (volume : Measure ℝ).restrict (Icc 0 (2 * Real.pi))))
    convert hh using 1
    funext θ
    rw [Finset.prod_mul_distrib]
    ring

theorem norm_polynomialTaylor_le {k : ℕ} (P : MvPolynomial (Fin k) ℂ) (h : Fin k → ℕ)
    (R D : ℝ) (hR : 0 < R)
    (hf : ∀ z, (∀ r, ‖z r‖ = R) → ‖exponentialPolynomial P h z‖ ≤ D) (d : Fin k → ℕ) :
    ‖polynomialTaylor P h R d‖ ≤ D := by
  rw [← coefficient_exponentialPolynomial P h R hR]
  exact norm_coefficient_le _ R D hR hf d

end
end GeneralizedLogarithms.MultivariateCauchyCoefficient

/-- info: 'GeneralizedLogarithms.MultivariateCauchyCoefficient.norm_polynomialTaylor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCauchyCoefficient.norm_polynomialTaylor_le
