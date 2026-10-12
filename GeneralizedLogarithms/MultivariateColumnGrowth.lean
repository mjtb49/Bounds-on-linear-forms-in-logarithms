import LogIrrationalityMeasure.Analysis.PeriodAnalytic

/-!
# Growth of the actual multilogarithmic exponential polynomials

The bound retains `-sum w_i * gamma_i`. Dropping this term would prevent the
large-transverse-order part of the determinant estimate from closing.
-/

namespace GeneralizedLogarithms.MultivariateColumnGrowth

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent

variable {k m : ℕ}

def columnFunction (a : Fin m → Fin k → ℤ) (h : Fin k → ℕ)
    (b γ : Fin m → ℕ) (z : Fin k → ℂ) : ℂ :=
  ((∏ i, (b i).choose (γ i) : ℕ) : ℂ) *
    Complex.exp (∑ r, (h r : ℂ) * z r) * ∏ i, (∑ r, (a i r : ℂ) * z r) ^ (b i - γ i)

theorem norm_linearForm_le (a : Fin k → ℤ) (w R : ℝ) (hR : 0 ≤ R)
    (ha : ∀ r, ‖(a r : ℂ)‖ ≤ Real.exp w) (z : Fin k → ℂ) (hz : ∀ r, ‖z r‖ ≤ R) :
    ‖∑ r, (a r : ℂ) * z r‖ ≤ (k : ℝ) * R * Real.exp w := by
  calc
    _ ≤ ∑ r, ‖(a r : ℂ) * z r‖ := norm_sum_le _ _
    _ ≤ ∑ _r : Fin k, Real.exp w * R := by
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul]
      exact mul_le_mul (ha r) (hz r) (norm_nonneg _) (Real.exp_pos w).le
    _ = _ := by simp; ring

theorem norm_columnFunction_le (a : Fin m → Fin k → ℤ) (h : Fin k → ℕ)
    (b γ : Fin m → ℕ) (w : Fin m → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i))
    (z : Fin k → ℂ) (hz : ∀ r, ‖z r‖ ≤ R) :
    ‖columnFunction a h b γ z‖ ≤ (2 : ℝ) ^ (∑ i, b i) *
      Real.exp (R * ∑ r, (h r : ℝ)) *
        ((k : ℝ) * R) ^ (∑ i, (b i - γ i)) * Real.exp (∑ i, w i * ((b i - γ i : ℕ) : ℝ)) := by
  have hb : ‖((∏ i, (b i).choose (γ i) : ℕ) : ℂ)‖ ≤ (2 : ℝ) ^ (∑ i, b i) := by
    exact PeriodAnalytic.norm_binomial_product_le b (RowTranslation.multiIndex γ)
  have hexp : ‖Complex.exp (∑ r, (h r : ℂ) * z r)‖ ≤ Real.exp (R * ∑ r, (h r : ℝ)) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ r, ‖(h r : ℂ) * z r‖ := norm_sum_le _ _
      _ ≤ ∑ r, (h r : ℝ) * R := by
        apply Finset.sum_le_sum
        intro r hr
        simp only [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (hz r) (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hp : ‖∏ i, (∑ r, (a i r : ℂ) * z r) ^ (b i - γ i)‖ ≤
      ((k : ℝ) * R) ^ (∑ i, (b i - γ i)) * Real.exp (∑ i, w i * ((b i - γ i : ℕ) : ℝ)) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ i, ((k : ℝ) * R * Real.exp (w i)) ^ (b i - γ i) := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i hi
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_linearForm_le (a i) (w i) R hR (ha i) z hz) _
      _ = _ := by
        simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        congr 1
        simp_rw [← Real.exp_nat_mul, mul_comm (w _) (_ : ℝ)]
        exact (Real.exp_sum _ _).symm
  rw [columnFunction, norm_mul, norm_mul]
  have hh := mul_le_mul (mul_le_mul hb hexp (norm_nonneg _) (by positivity)) hp
    (norm_nonneg _) (by positivity)
  simpa only [mul_assoc] using hh

theorem exponent_budget (h : Fin k → ℕ) (b γ : Fin m → ℕ) (w : Fin m → ℝ)
    (H R w₀ wstar G : ℝ) (hH : 0 ≤ H) (hR : 0 ≤ R) (hw₀ : 0 < w₀) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hγ : ∀ i, γ i ≤ b i)
    (hcol : w₀ * (∑ r, (h r : ℝ)) + ∑ i, w i * b i ≤ H) (hG : 1 ≤ G) :
    (∑ i, w i * ((b i - γ i : ℕ) : ℝ)) + R * (∑ r, (h r : ℝ)) +
        (∑ i, (b i : ℝ)) * Real.log G ≤
      H - (∑ i, w i * γ i) + H * (R / w₀ + Real.log G / wstar) := by
  have hwpos i : 0 ≤ w i := hws.le.trans (hw i)
  have hsum : 0 ≤ ∑ i, w i * b i := Finset.sum_nonneg fun i _ => mul_nonneg (hwpos i) (Nat.cast_nonneg _)
  have hy : (∑ r, (h r : ℝ)) ≤ H / w₀ := by
    apply (le_div_iff₀ hw₀).mpr
    nlinarith
  have hx : (∑ i, (b i : ℝ)) ≤ H / wstar := by
    apply (le_div_iff₀ hws).mpr
    have hh : wstar * (∑ i, (b i : ℝ)) ≤ ∑ i, w i * b i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
    have hlong : 0 ≤ w₀ * ∑ r, (h r : ℝ) := mul_nonneg hw₀.le (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    nlinarith
  have hdiff : (∑ i, w i * ((b i - γ i : ℕ) : ℝ)) = (∑ i, w i * b i) - ∑ i, w i * γ i := by
    simp_rw [Nat.cast_sub (hγ _), mul_sub, Finset.sum_sub_distrib]
  rw [hdiff]
  have hyR := mul_le_mul_of_nonneg_left hy hR
  have hxG := mul_le_mul_of_nonneg_right hx (Real.log_nonneg hG)
  have hlong : 0 ≤ w₀ * ∑ r, (h r : ℝ) := mul_nonneg hw₀.le (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  calc
    _ ≤ H - (∑ i, w i * γ i) + R * (H / w₀) + (H / wstar) * Real.log G := by linarith
    _ = _ := by ring

theorem norm_columnFunction_exp_budget (hk : 0 < k)
    (a : Fin m → Fin k → ℤ) (h : Fin k → ℕ) (b γ : Fin m → ℕ) (w : Fin m → ℝ)
    (H R w₀ wstar : ℝ) (hH : 0 ≤ H) (hR : 1 ≤ R) (hw₀ : 0 < w₀) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hγ : ∀ i, γ i ≤ b i)
    (hcol : w₀ * (∑ r, (h r : ℝ)) + ∑ i, w i * b i ≤ H)
    (ha : ∀ i r, ‖(a i r : ℂ)‖ ≤ Real.exp (w i))
    (z : Fin k → ℂ) (hz : ∀ r, ‖z r‖ ≤ R) :
    ‖columnFunction a h b γ z‖ ≤
      Real.exp (H - (∑ i, w i * γ i) + H * (R / w₀ + Real.log (2 * k * R) / wstar)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR : (1 : ℝ) ≤ k * R := one_le_mul_of_one_le_of_one_le hk1 hR
  have hG : (1 : ℝ) ≤ 2 * k * R := by nlinarith
  have hdegree : (∑ i, (b i - γ i)) ≤ ∑ i, b i := Finset.sum_le_sum fun i _ => Nat.sub_le _ _
  calc
    _ ≤ (2 : ℝ) ^ (∑ i, b i) * Real.exp (R * ∑ r, (h r : ℝ)) *
        ((k : ℝ) * R) ^ (∑ i, (b i - γ i)) * Real.exp (∑ i, w i * ((b i - γ i : ℕ) : ℝ)) :=
      norm_columnFunction_le a h b γ w R (zero_le_one.trans hR) ha z hz
    _ ≤ (2 : ℝ) ^ (∑ i, b i) * Real.exp (R * ∑ r, (h r : ℝ)) *
        ((k : ℝ) * R) ^ (∑ i, b i) * Real.exp (∑ i, w i * ((b i - γ i : ℕ) : ℝ)) := by
      gcongr
    _ = Real.exp ((∑ i, w i * ((b i - γ i : ℕ) : ℝ)) + R * (∑ r, (h r : ℝ)) +
        (∑ i, (b i : ℝ)) * Real.log (2 * k * R)) := by
      rw [Real.exp_add, Real.exp_add,
        show (∑ i, (b i : ℝ)) = ((∑ i, b i : ℕ) : ℝ) from (Nat.cast_sum _ _).symm,
        Real.exp_nat_mul, Real.exp_log (by positivity)]
      rw [show (2 : ℝ) * k * R = 2 * ((k : ℝ) * R) by ring, mul_pow]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (exponent_budget h b γ w H R w₀ wstar (2 * k * R)
      hH (zero_le_one.trans hR) hw₀ hws hw hγ hcol hG)

end
end GeneralizedLogarithms.MultivariateColumnGrowth

/-- info: 'GeneralizedLogarithms.MultivariateColumnGrowth.norm_columnFunction_exp_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateColumnGrowth.norm_columnFunction_exp_budget
