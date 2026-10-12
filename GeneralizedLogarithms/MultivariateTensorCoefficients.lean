import GeneralizedLogarithms.MultivariateFormalJet
import GeneralizedLogarithms.MultivariateAnalyticSeries

/-!
# Coefficients of products in independent formal variables

This identifies the tensor analytic row with a coefficient of the actual
multivariate formal exponential-polynomial expression.
-/

namespace GeneralizedLogarithms.MultivariateTensorCoefficients

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateAnalyticSeries

theorem coeff_prod_lift {σ R : Type*} [Fintype σ] [CommRing R]
    (f : σ → PowerSeries R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (∏ i, (f i).toMvPowerSeries i) = ∏ i, PowerSeries.coeff (d i) (f i) := by
  classical
  let l₀ : σ →₀ (σ →₀ ℕ) := Finsupp.equivFunOnFinite.symm (fun i => Finsupp.single i (d i))
  have hl₀ : l₀ ∈ Finset.finsuppAntidiag Finset.univ d := by
    apply Finset.mem_finsuppAntidiag.mpr
    refine ⟨?_, Finset.subset_univ _⟩
    simpa [l₀] using Finsupp.univ_sum_single d
  have huniq (l : σ →₀ (σ →₀ ℕ)) (hl : l ∈ Finset.finsuppAntidiag Finset.univ d)
      (hc : ∀ i, l i = Finsupp.single i (l i i)) : l = l₀ := by
    have hs := (Finset.mem_finsuppAntidiag.mp hl).1
    have hd (i : σ) : l i i = d i := by
      have hh := DFunLike.congr_fun hs i
      simp only [Finsupp.finsetSum_apply] at hh
      have he : (∑ r, l r i) = l i i := by
        calc
          _ = ∑ r, (Finsupp.single r (l r r)) i :=
            Finset.sum_congr rfl (fun r _ => DFunLike.congr_fun (hc r) i)
          _ = _ := by simp [Finsupp.single_apply]
      exact he.symm.trans hh
    ext i
    rw [hc, hd]
    rfl
  rw [MvPowerSeries.coeff_prod, Finset.sum_eq_single l₀]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.coeff_subst_single, l₀]
  · intro l hl hne
    by_contra hn
    apply hne
    apply huniq l hl
    intro i
    have hh : MvPowerSeries.coeff (l i) ((f i).toMvPowerSeries i) ≠ 0 :=
      fun hz => hn (Finset.prod_eq_zero (Finset.mem_univ i) hz)
    by_contra hbad
    exact hh (by simp only [PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.coeff_subst_single,
      ite_eq_right hbad])
  · exact fun hn => (hn hl₀).elim

variable {k : ℕ}

def periodVector (ω : Fin k → ℂ) (j : ℕ) (r : Fin k) : MvPowerSeries (Fin k) ℂ :=
  MvPowerSeries.C ((j : ℂ) * ω r) + (PowerSeries.log ℂ).toMvPowerSeries r

def exponentialFactor (y : Fin k → ℂ) (j : ℕ) (h : Fin k → ℕ) : MvPowerSeries (Fin k) ℂ :=
  ∏ r, (MvPowerSeries.C (y r ^ j) * (1 + MvPowerSeries.X r)) ^ h r

def formalPolynomialRow (P : MvPolynomial (Fin k) ℂ) (h : Fin k → ℕ)
    (ω y : Fin k → ℂ) (j : ℕ) : MvPowerSeries (Fin k) ℂ :=
  exponentialFactor y j h * MvPolynomial.aeval (periodVector ω j) P

theorem formal_monomial_tensor (h : Fin k → ℕ) (e : Fin k →₀ ℕ)
    (ω y : Fin k → ℂ) (j : ℕ) :
    exponentialFactor y j h * ∏ r, periodVector ω j r ^ e r =
      ∏ r, (PeriodAnalytic.periodSeries ((y r ^ j) ^ h r) ((j : ℂ) * ω r) (h r) (e r)).toMvPowerSeries r := by
  rw [exponentialFactor, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r hr
  simp only [PeriodAnalytic.periodSeries, map_mul, map_pow, map_add, map_one,
    PowerSeries.toMvPowerSeries_C, PowerSeries.toMvPowerSeries_X, periodVector, mul_pow]

theorem coeff_formalPolynomialRow (P : MvPolynomial (Fin k) ℂ) (h : Fin k → ℕ)
    (ω y : Fin k → ℂ) (j : ℕ) (ell : Fin k →₀ ℕ) :
    MvPowerSeries.coeff ell (formalPolynomialRow P h ω y j) = polynomialRow P h ω y j ell := by
  classical
  conv_lhs => rw [formalPolynomialRow, P.as_sum]
  simp only [map_sum, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finset.mul_sum, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [polynomialRow]
  apply Finset.sum_congr rfl
  intro e he
  rw [show exponentialFactor y j h * (MvPowerSeries.C (P.coeff e) * ∏ r, periodVector ω j r ^ e r) =
      MvPowerSeries.C (P.coeff e) * (exponentialFactor y j h * ∏ r, periodVector ω j r ^ e r) by ring,
    MvPowerSeries.coeff_C_mul, formal_monomial_tensor, coeff_prod_lift]

theorem hasSum_formalPolynomialRow (P : MvPolynomial (Fin k) ℂ) (h : Fin k → ℕ)
    (ω y : Fin k → ℂ) (hy : ∀ r, Complex.exp (ω r) = y r)
    (j : ℕ) (R : NNReal) (hR : 0 < R)
    (hc : ∀ r, ‖(j : ℂ) * ω r‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : Fin k →₀ ℕ) :
    HasSum (fun d => rowTestTensor (fun r => (j : ℂ) * ω r) R ell d * polynomialTaylor P h R d)
      (MvPowerSeries.coeff ell (formalPolynomialRow P h ω y j)) := by
  rw [coeff_formalPolynomialRow]
  exact hasSum_polynomial_row P h ω y hy j R hR hc ell

end
end GeneralizedLogarithms.MultivariateTensorCoefficients

/-- info: 'GeneralizedLogarithms.MultivariateTensorCoefficients.hasSum_formalPolynomialRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateTensorCoefficients.hasSum_formalPolynomialRow
