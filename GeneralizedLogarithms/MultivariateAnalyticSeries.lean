import LogIrrationalityMeasure.Analysis.AnalyticRowSeries
import LogIrrationalityMeasure.Analysis.PeriodAnalytic

/-!
# Tensor Taylor expansions for exponential polynomials

Each coordinate uses the original one-variable analytic theorem. Finite
products of its absolutely convergent sums give the full Taylor multi-index;
finite polynomial linear combinations preserve the row identity.
-/

namespace GeneralizedLogarithms.MultivariateAnalyticSeries

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open AnalyticCollision

theorem hasSum_mul_complex {ι κ : Type*} (f : ι → ℂ) (g : κ → ℂ) (x y : ℂ)
    (hf : HasSum f x) (hg : HasSum g y) :
    HasSum (fun d : ι × κ => f d.1 * g d.2) (x * y) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

theorem hasSum_fin_product {k : ℕ} (f : Fin k → ℕ → ℂ) (v : Fin k → ℂ)
    (hf : ∀ r, HasSum (f r) (v r)) :
    HasSum (fun d : Fin k → ℕ => ∏ r, f r (d r)) (∏ r, v r) := by
  induction k with
  | zero => simpa using hasSum_fintype (fun d : Fin 0 → ℕ => ∏ r, f r (d r))
  | succ k ih =>
    have ht := ih (fun r => f r.succ) (fun r => v r.succ) (fun r => hf r.succ)
    have hh : HasSum (fun d : ℕ × (Fin k → ℕ) => f 0 d.1 * ∏ r : Fin k, f r.succ (d.2 r))
        (v 0 * ∏ r : Fin k, v r.succ) :=
      hasSum_mul_complex (f 0) (fun d : Fin k → ℕ => ∏ r : Fin k, f r.succ (d r)) _ _ (hf 0) ht
    apply (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ] using hh

variable {k : ℕ}

def rowTestTensor (center : Fin k → ℂ) (R : ℝ) (ell d : Fin k → ℕ) : ℂ :=
  ∏ r, rowTest (ell r) (fun t => ((center r + Complex.log (1 + t)) / (R : ℂ)) ^ d r)

def taylorTensor (f : Fin k → ℂ → ℂ) (R : ℝ) (d : Fin k → ℕ) : ℂ :=
  ∏ r, normalizedTaylorCoeff (f r) R (d r)

theorem hasSum_tensor_row (f : Fin k → ℂ → ℂ) (hf : ∀ r, Differentiable ℂ (f r))
    (R : NNReal) (hR : 0 < R) (D : Fin k → ℝ) (hD : ∀ r, 0 ≤ D r)
    (hfD : ∀ r z, z ∈ Metric.sphere (0 : ℂ) R → ‖f r z‖ ≤ D r)
    (center : Fin k → ℂ) (hc : ∀ r, ‖center r‖ + 3 / 4 ≤ (R : ℝ) / 2)
    (ell : Fin k → ℕ) :
    HasSum (fun d : Fin k → ℕ => rowTestTensor center R ell d * taylorTensor f R d)
      (∏ r, rowTest (ell r) (fun t => f r (center r + Complex.log (1 + t)))) := by
  have hh := hasSum_fin_product
    (fun r d => rowTest (ell r) (fun t => ((center r + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
      normalizedTaylorCoeff (f r) R d)
    (fun r => rowTest (ell r) (fun t => f r (center r + Complex.log (1 + t))))
    (fun r => hasSum_translated_row (hf r) hR (hD r) (hfD r) (hc r) (ell r))
  simpa only [Finset.prod_mul_distrib, rowTestTensor, taylorTensor] using hh

theorem norm_rowTestTensor_le (center : Fin k → ℂ) (R : ℝ) (hR : 0 < R)
    (hc : ∀ r, ‖center r‖ + 3 / 4 ≤ R / 2) (ell d : Fin k → ℕ) :
    ‖rowTestTensor center R ell d‖ ≤ (2 : ℝ) ^ (∑ r, ell r) * (1 / 2 : ℝ) ^ (∑ r, d r) := by
  rw [rowTestTensor, norm_prod]
  calc
    _ ≤ ∏ r, (2 : ℝ) ^ ell r * (1 / 2 : ℝ) ^ d r :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun r _ => norm_rowTest_shifted_power_le hR (hc r) _ _)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

theorem norm_taylorTensor_le (f : Fin k → ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (D : Fin k → ℝ) (hfD : ∀ r z, z ∈ Metric.sphere (0 : ℂ) R → ‖f r z‖ ≤ D r)
    (d : Fin k → ℕ) : ‖taylorTensor f R d‖ ≤ ∏ r, D r := by
  rw [taylorTensor, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun r _ => norm_normalizedTaylorCoeff_le hR (hfD r) _)

def exponentialFactors (h : Fin k → ℕ) (e : Fin k →₀ ℕ) (r : Fin k) : ℂ → ℂ :=
  exponentialMonomial 1 (h r) (e r)

def polynomialTaylor (P : MvPolynomial (Fin k) ℂ) (h : Fin k → ℕ) (R : ℝ)
    (d : Fin k → ℕ) : ℂ :=
  ∑ e ∈ P.support, P.coeff e * taylorTensor (exponentialFactors h e) R d

def polynomialRow (P : MvPolynomial (Fin k) ℂ) (h : Fin k → ℕ)
    (ω y : Fin k → ℂ) (j : ℕ) (ell : Fin k → ℕ) : ℂ :=
  ∑ e ∈ P.support, P.coeff e * ∏ r, PowerSeries.coeff (ell r)
    (PeriodAnalytic.periodSeries ((y r ^ j) ^ h r) ((j : ℂ) * ω r) (h r) (e r))

theorem hasSum_polynomial_row (P : MvPolynomial (Fin k) ℂ) (h : Fin k → ℕ)
    (ω y : Fin k → ℂ) (hy : ∀ r, Complex.exp (ω r) = y r)
    (j : ℕ) (R : NNReal) (hR : 0 < R)
    (hc : ∀ r, ‖(j : ℂ) * ω r‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : Fin k → ℕ) :
    HasSum (fun d => rowTestTensor (fun r => (j : ℂ) * ω r) R ell d * polynomialTaylor P h R d)
      (polynomialRow P h ω y j ell) := by
  have ht (e : Fin k →₀ ℕ) := hasSum_tensor_row (exponentialFactors h e)
    (fun r => differentiable_exponentialMonomial _ _ _) R hR
    (fun r => Real.exp ((h r : ℝ) * R) * (R : ℝ) ^ e r) (fun r => by positivity)
    (fun r z hz => by
      simpa only [exponentialFactors, norm_one, one_mul, Complex.norm_natCast] using
        norm_exponentialMonomial_le (1 : ℂ) (h r) (e r) (NNReal.coe_nonneg R)
          (show ‖z‖ ≤ R by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le))
    (fun r => (j : ℂ) * ω r) hc ell
  have hh := hasSum_sum (s := P.support) (fun e _ => (ht e).mul_left (P.coeff e))
  simp_rw [exponentialFactors, PeriodAnalytic.rowTest_exponentialMonomial_eq_coeff _ _ _ (hy _),
    one_mul] at hh
  change HasSum _ (∑ e ∈ P.support, P.coeff e * ∏ r, PowerSeries.coeff (ell r)
    (PeriodAnalytic.periodSeries ((y r ^ j) ^ h r) ((j : ℂ) * ω r) (h r) (e r)))
  convert hh using 1
  funext d
  simp only [polynomialTaylor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

end
end GeneralizedLogarithms.MultivariateAnalyticSeries

/-- info: 'GeneralizedLogarithms.MultivariateAnalyticSeries.hasSum_tensor_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAnalyticSeries.hasSum_tensor_row

/-- info: 'GeneralizedLogarithms.MultivariateAnalyticSeries.hasSum_polynomial_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateAnalyticSeries.hasSum_polynomial_row
