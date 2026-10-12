import GeneralizedLogarithms.MultivariateNormalizedRows
import GeneralizedLogarithms.MultivariateDeterminantDichotomy
import GeneralizedLogarithms.MultivariateMatrixTranslation

/-! Exponential decay for each determinant in the actual row translation. -/

namespace GeneralizedLogarithms.MultivariateTranslatedDeterminant

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateRowTranslation MultivariateColumnSeries MultivariateNormalizedRows
open MatrixTranslationBounds

variable {k m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_det_row_sum_le {δ : ι → Type*} [∀ i, Fintype (δ i)]
    (T : ∀ i, δ i → ι → ℂ) (B : ℝ)
    (hB : ∀ f : (∀ i, δ i), ‖Matrix.det (fun i j => T i (f i) j)‖ ≤ B) :
    ‖Matrix.det (fun i j => ∑ t, T i t j)‖ ≤
      (∏ i, (Fintype.card (δ i) : ℝ))*B := by
  have he := MatrixTranslation.det_dependent_row_sum (fun i (_ : δ i) => (1 : ℂ)) T
  simp only [one_mul, Finset.prod_const_one] at he
  rw [he]
  calc
    _ ≤ ∑ f : (∀ i, δ i), ‖Matrix.det (fun i j => T i (f i) j)‖ := norm_sum_le _ _
    _ ≤ ∑ _f : (∀ i, δ i), B := Finset.sum_le_sum (fun f _ => hB f)
    _ = _ := by simp [Fintype.card_pi, Nat.cast_prod]

def columnLoss (k : ℕ) (R w₀ ws : ℝ) : ℝ :=
  1+R/w₀+Real.log (2*k*R)/ws

theorem norm_translated_det_le (hk : 0 < k)
    (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ) (T : Fin m → ℕ)
    (y ω : Fin k → ℂ) (hy : ∀ r, Complex.exp (ω r) = y r)
    (j : ι → ℕ) (β γ : ι → Fin m →₀ ℕ)
    (d : ∀ i, ∀ t, Fin (γ i t - β i t + 1)) (s ell : ι → Fin k →₀ ℕ)
    (h : ι → Fin k →₀ ℕ) (b : ι → Fin m →₀ ℕ)
    (w : Fin m → ℝ) (R : NNReal) (H w₀ ws v₀ F ν C θ A η S c : ℝ)
    (hH : 0 ≤ H) (hR : 1 ≤ (R : ℝ)) (hw₀ : 0 < w₀) (hws : 0 < ws)
    (hv₀ : 0 < v₀) (hF : 0 < F) (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hS : 0 ≤ S)
    (hw : ∀ i, ws ≤ w i) (hT : ∀ i, 1 ≤ T i) (hTw : ∀ i, F*w i ≤ v₀*T i)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i))
    (herror : ∀ i t, ‖error a p ω (j i) t‖ ≤ Real.exp (C-ν*w t))
    (hcenter : ∀ i r, ‖(j i : ℂ)*ω r‖+3/4 ≤ (R : ℝ)/2)
    (hcol : ∀ l, w₀*(∑ r, (h l r : ℝ))+∑ i, w i*b l i ≤ H)
    (hβ : ∀ i, weight w (β i) ≤ θ*H) (hγ : ∀ i, weight w (γ i) ≤ H)
    (hs : ∀ i, ((s i).degree : ℝ) ≤ H/v₀) (hell : ∀ i, ((ell i).degree : ℝ) ≤ H/v₀)
    (capacity : Finset ((Fin m →₀ ℕ) × (Fin k → ℕ)))
    (hcover : ∀ (g : Fin m →₀ ℕ) (n : Fin k → ℕ), weight w g ≤ A*H → (∑ r, (n r : ℝ)) < S*H → (g,n) ∈ capacity)
    (hcapacity : (capacity.card : ℝ) ≤ η*Fintype.card ι/2)
    (hhighgap : columnLoss k R w₀ ws+ν*θ+rowLoss k ν C ws v₀ F-(ν+1)*(1-η)*A ≤ -c)
    (hlowgap : columnLoss k R w₀ ws+ν*θ+rowLoss k ν C ws v₀ F+Real.log (3/4)*η*S/2 ≤ -c) :
    ‖Matrix.det (fun i l =>
      rowScalar (error a p ω (j i)) (tail a T) (β i) (γ i) (d i) (s i) *
        MvPowerSeries.coeff (ell i) ((periodMonomial y ω a (j i) (h l) (b l)).coeff (γ i)))‖ ≤
      (Fintype.card ι).factorial *
        Real.exp (-(Fintype.card ι : ℝ)*H*c+(k*Fintype.card ι : ℕ)*Real.log 4) := by
  let B := fun i n => rowFactor a (error a p ω (j i)) T (β i) (γ i) (d i) (s i) (ell i)
    w (fun r => (j i : ℂ)*ω r) R n
  let Cf := fun g n l => normalizedCoefficient a (h l) (b l) g w R n
  apply MultivariateDeterminantDichotomy.norm_det_le γ (fun g => weight w g) B Cf capacity
    A η S H (ν+1) (columnLoss k R w₀ ws) (ν*θ+rowLoss k ν C ws v₀ F) c
    (fun g => Finset.sum_nonneg (fun i _ => mul_nonneg (hws.le.trans (hw i)) (Nat.cast_nonneg _)))
    hA hS hH (by linarith)
  · intro g n l
    exact norm_normalizedCoefficient_le hk a (h l) (b l) g w H R w₀ ws
      hH hR hw₀ hws hw (hcol l) ha n
  · intro i n
    have hh := norm_rowFactor_le a (error a p ω (j i)) T (β i) (γ i) (d i) (s i) (ell i)
      w (fun r => (j i : ℂ)*ω r) R ν C H ws v₀ F hC hν hws hv₀ hF hw (hγ i)
      (hs i) (hell i) hT hTw ha (herror i) (zero_lt_one.trans_le hR) (hcenter i) n
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hβ i) hν]
  · exact hcover
  · exact hcapacity
  · simpa only [add_assoc] using hhighgap
  · simpa only [add_assoc] using hlowgap
  · intro i l
    exact hasSum_rowFactor a (error a p ω (j i)) T (β i) (γ i) (d i) (s i) (ell i)
      w y ω hy (j i) (h l) (b l) R (by exact_mod_cast zero_lt_one.trans_le hR) (hcenter i)

end
end GeneralizedLogarithms.MultivariateTranslatedDeterminant

/-- info: 'GeneralizedLogarithms.MultivariateTranslatedDeterminant.norm_translated_det_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateTranslatedDeterminant.norm_translated_det_le
