import GeneralizedLogarithms.MultivariateTailNorm
import GeneralizedLogarithms.MultivariateTailBudget
import LogIrrationalityMeasure.Approximation.MatrixTranslationBounds

/-!
# Bounds for the actual multivariate row-translation scalars

The extra integer matrix coefficients in the tails contribute one additional
unit to the cutoff cost: `(nu+1)/F` instead of `nu/F`.
-/

namespace GeneralizedLogarithms.MultivariateRowScalarBounds

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateRowTranslation MatrixTranslationBounds

variable {k m : ℕ}

theorem norm_rowScalar_exp_basic (a : Fin m → Fin k → ℤ) (ε : Fin m → ℂ)
    (T : Fin m → ℕ) (β A : Fin m →₀ ℕ) (d : ∀ i, Fin (A i - β i + 1))
    (s : Fin k →₀ ℕ) (w : Fin m → ℝ) (C ν : ℝ)
    (hT : ∀ i, 1 ≤ T i) (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i))
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (tail a T) β A d s‖ ≤
      Real.exp (((∑ i, A i : ℕ) : ℝ) * Real.log 4 +
        (∑ i, ((A i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) +
        ((∑ i, (d i : ℕ) : ℕ) : ℝ) * Real.log (max 1 (k : ℝ)) +
        weight w (fun i => (d i : ℕ)) + (s.degree : ℝ) * Real.log 2) := by
  have hb : ‖((∏ i, (A i).choose (β i) * (A i - β i).choose (d i) : ℕ) : ℂ)‖ ≤
      (4 : ℝ) ^ (∑ i, A i) := by
    rw [Complex.norm_natCast]
    exact_mod_cast RowTranslation.multi_choose_product_le_four_pow A β (fun i => (d i : ℕ))
  have ht := MultivariateTailNorm.norm_coeff_tail_product a T (fun i => (d i : ℕ)) hT w ha s
  have hkpow : (k : ℝ) ^ (∑ i, (d i : ℕ)) ≤ (max 1 (k : ℝ)) ^ (∑ i, (d i : ℕ)) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) _
  have ht' : ‖MvPowerSeries.coeff s (∏ i, tail a T i ^ (d i : ℕ))‖ ≤
      (max 1 (k : ℝ)) ^ (∑ i, (d i : ℕ)) * Real.exp (weight w (fun i => (d i : ℕ))) *
        (2 : ℝ) ^ s.degree := by
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hkpow (Real.exp_pos _).le) (by positivity))
  simp only [rowScalar, norm_mul, norm_prod, norm_pow]
  have hh := mul_le_mul (mul_le_mul hb (error_power_product_le ε (fun i => A i - β i - d i) w C ν hε)
      (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _) (by positivity)) ht'
      (norm_nonneg _) (by positivity)
  apply hh.trans
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
    Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
  exact le_of_eq (by ring)

theorem norm_rowScalar_exp_weight_difference (a : Fin m → Fin k → ℤ) (ε : Fin m → ℂ)
    (T : Fin m → ℕ) (β A : Fin m →₀ ℕ) (d : ∀ i, Fin (A i - β i + 1))
    (s : Fin k →₀ ℕ) (w : Fin m → ℝ) (C ν H ws v₀ F : ℝ)
    (hC : 0 ≤ C) (hν : 0 ≤ ν) (hws : 0 < ws) (hv₀ : 0 < v₀) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (hA : weight w A ≤ H) (hs : (s.degree : ℝ) ≤ H / v₀)
    (hT : ∀ i, 1 ≤ T i) (hTw : ∀ i, F * w i ≤ v₀ * T i)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i))
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (tail a T) β A d s‖ ≤
      Real.exp (-ν * (weight w A - weight w β) +
        H * ((ν + 1) / F + Real.log 2 / v₀ + (Real.log 4 + C + Real.log (max 1 (k : ℝ))) / ws)) := by
  by_cases hz : MvPowerSeries.coeff s (∏ i, tail a T i ^ (d i : ℕ)) = 0
  · simp [rowScalar, hz, Real.exp_nonneg]
  have hbudget : weight w (fun i => (d i : ℕ)) ≤ H / F := by
    have hb := MultivariateTailBudget.tail_weight_budget a T (fun i => (d i : ℕ)) s w v₀ F hv₀.le hF hTw hz
    have hb' : weight w (fun i => (d i : ℕ)) ≤ v₀ * s.degree / F := by
      simpa only [weight, mul_comm] using hb
    have hh : v₀ * (s.degree : ℝ) ≤ H := by nlinarith [(le_div_iff₀ hv₀).mp hs]
    exact hb'.trans (div_le_div_of_nonneg_right hh hF.le)
  have hsize := sum_exponents_le w A H ws hws hw hA
  have hcount : ((∑ i, (A i - β i - d i) : ℕ) : ℝ) ≤ ((∑ i, A i : ℕ) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum (fun i _ => (Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have hdcount : ((∑ i, (d i : ℕ) : ℕ) : ℝ) ≤ ((∑ i, A i : ℕ) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum (fun i _ =>
      (Nat.le_of_lt_succ (d i).isLt).trans (Nat.sub_le _ _))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogk : 0 ≤ Real.log (max 1 (k : ℝ)) := Real.log_nonneg (le_max_left _ _)
  have hdiff := weight_sub_le_weight_tsub w A β (fun i => hws.le.trans (hw i))
  apply (norm_rowScalar_exp_basic a ε T β A d s w C ν hT ha hε).trans
  apply Real.exp_le_exp.mpr
  rw [residual_exponent_identity]
  calc
    _ ≤ (Real.log 4 + C + Real.log (max 1 (k : ℝ))) * ((∑ i, A i : ℕ) : ℝ) -
        ν * (weight w A - weight w β) + (ν + 1) * (H / F) + (H / v₀) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcount hC,
        mul_le_mul_of_nonneg_right hdcount hlogk,
        mul_le_mul_of_nonneg_left hdiff hν,
        mul_le_mul_of_nonneg_left hbudget (by linarith : 0 ≤ ν + 1),
        mul_le_mul_of_nonneg_right hs hlog2]
    _ ≤ (Real.log 4 + C + Real.log (max 1 (k : ℝ))) * (H / ws) -
        ν * (weight w A - weight w β) + (ν + 1) * (H / F) + (H / v₀) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ Real.log 4 + C + Real.log (max 1 (k : ℝ)))]
    _ = _ := by ring

end
end GeneralizedLogarithms.MultivariateRowScalarBounds

/-- info: 'GeneralizedLogarithms.MultivariateRowScalarBounds.norm_rowScalar_exp_weight_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateRowScalarBounds.norm_rowScalar_exp_weight_difference
