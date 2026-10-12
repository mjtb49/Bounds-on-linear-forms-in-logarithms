import GeneralizedLogarithms.MultivariateRowScalarBounds
import GeneralizedLogarithms.MultivariateColumnSeries

/-! Normalized row factors for the actual Taylor expansion. -/

namespace GeneralizedLogarithms.MultivariateNormalizedRows

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateRowTranslation MultivariateColumnSeries MultivariateAnalyticSeries
open MatrixTranslationBounds

variable {k m : ℕ}

def rowFactor (a : Fin m → Fin k → ℤ) (ε : Fin m → ℂ) (T : Fin m → ℕ)
    (β γ : Fin m →₀ ℕ) (d : ∀ i, Fin (γ i - β i + 1)) (s ell : Fin k →₀ ℕ)
    (w : Fin m → ℝ) (center : Fin k → ℂ) (R : ℝ) (n : Fin k → ℕ) : ℂ :=
  rowScalar ε (tail a T) β γ d s * (Real.exp (-weight w γ) : ℂ) *
    rowTestTensor center R ell n

def rowLoss (k : ℕ) (ν C ws v₀ F : ℝ) : ℝ :=
  (ν+1)/F + 2*Real.log 2/v₀ + (Real.log 4+C+Real.log (max 1 (k : ℝ)))/ws

theorem hasSum_rowFactor (a : Fin m → Fin k → ℤ) (ε : Fin m → ℂ) (T : Fin m → ℕ)
    (β γ : Fin m →₀ ℕ) (d : ∀ i, Fin (γ i - β i + 1)) (s ell : Fin k →₀ ℕ)
    (w : Fin m → ℝ) (y ω : Fin k → ℂ) (hy : ∀ r, Complex.exp (ω r) = y r)
    (j : ℕ) (h : Fin k →₀ ℕ) (b : Fin m →₀ ℕ) (R : NNReal) (hR : 0 < R)
    (hc : ∀ r, ‖(j : ℂ)*ω r‖+3/4 ≤ (R : ℝ)/2) :
    HasSum (fun n => rowFactor a ε T β γ d s ell w (fun r => (j : ℂ)*ω r) R n *
      normalizedCoefficient a h b γ w R n)
      (rowScalar ε (tail a T) β γ d s *
        MvPowerSeries.coeff ell ((periodMonomial y ω a j h b).coeff γ)) := by
  have hh := (hasSum_actual_period_coefficient y ω a hy j h b γ R hR hc ell).mul_left
    (rowScalar ε (tail a T) β γ d s)
  have he : (Real.exp (-weight w γ) : ℂ) * (Real.exp (∑ i, w i * γ i) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp [weight]
  convert hh using 1
  funext n
  dsimp only [rowFactor, normalizedCoefficient]
  calc
    _ = rowScalar ε (tail a T) β γ d s *
        ((Real.exp (-weight w γ) : ℂ) * (Real.exp (∑ i, w i * γ i) : ℂ)) *
        (rowTestTensor (fun r => (j : ℂ)*ω r) R ell n *
          polynomialTaylor (transversePolynomial a b γ) h R n) := by ring
    _ = _ := by rw [he, mul_one]

theorem norm_rowFactor_le (a : Fin m → Fin k → ℤ) (ε : Fin m → ℂ) (T : Fin m → ℕ)
    (β γ : Fin m →₀ ℕ) (d : ∀ i, Fin (γ i - β i + 1)) (s ell : Fin k →₀ ℕ)
    (w : Fin m → ℝ) (center : Fin k → ℂ) (R ν C H ws v₀ F : ℝ)
    (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws) (hv₀ : 0 < v₀) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (hγ : weight w γ ≤ H)
    (hs : (s.degree : ℝ) ≤ H/v₀) (hell : (ell.degree : ℝ) ≤ H/v₀)
    (hT : ∀ i, 1 ≤ T i) (hTw : ∀ i, F*w i ≤ v₀*T i)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i))
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C-ν*w i)) (hR : 0 < R)
    (hc : ∀ r, ‖center r‖+3/4 ≤ R/2) (n : Fin k → ℕ) :
    ‖rowFactor a ε T β γ d s ell w center R n‖ ≤
      Real.exp (-(ν+1)*weight w γ + ν*weight w β + H*rowLoss k ν C ws v₀ F) *
        (1/2 : ℝ)^(∑ r, n r) := by
  have hscalar := MultivariateRowScalarBounds.norm_rowScalar_exp_weight_difference
    a ε T β γ d s w C ν H ws v₀ F hC hν hws hv₀ hF hw hγ hs hT hTw ha hε
  have htest := norm_rowTestTensor_le center R hR hc ell n
  have hpow : (2 : ℝ)^(∑ r, ell r) ≤ Real.exp ((H/v₀)*Real.log 2) := by
    calc
      (2 : ℝ)^(∑ r, ell r) = Real.exp (((∑ r, ell r : ℕ) : ℝ)*Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ)<2)]
      _ ≤ _ := ?_
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by simpa [Finsupp.degree_eq_sum] using hell)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  rw [rowFactor, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (Real.exp (-ν*(weight w γ-weight w β)+
        H*((ν+1)/F+Real.log 2/v₀+(Real.log 4+C+Real.log (max 1 (k : ℝ)))/ws)) *
        Real.exp (-weight w γ)) *
        (Real.exp ((H/v₀)*Real.log 2) * (1/2 : ℝ)^(∑ r, n r)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hscalar (Real.exp_pos _).le)
        (htest.trans (mul_le_mul_of_nonneg_right hpow (by positivity)))
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← mul_assoc (Real.exp (-weight w γ)), ← Real.exp_add,
        ← mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [rowLoss]
      ring

end
end GeneralizedLogarithms.MultivariateNormalizedRows

/-- info: 'GeneralizedLogarithms.MultivariateNormalizedRows.hasSum_rowFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateNormalizedRows.hasSum_rowFactor

/-- info: 'GeneralizedLogarithms.MultivariateNormalizedRows.norm_rowFactor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateNormalizedRows.norm_rowFactor_le
