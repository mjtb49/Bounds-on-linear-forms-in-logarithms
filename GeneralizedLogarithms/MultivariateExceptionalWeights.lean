import GeneralizedLogarithms.GeneralPositionFamily
import GeneralizedLogarithms.MultivariateRowTranslation

/-! Weights attached to actual exceptional integer linear forms. -/

namespace GeneralizedLogarithms.MultivariateExceptionalWeights

noncomputable section
open scoped BigOperators
open LogIrrationalityMeasure.LogExponent

variable {k : ℕ}

def logarithmicWeight (p : ℤ) (a : Fin k → ℤ) : ℕ :=
  ⌈Real.log (coefficientHeight p a)⌉₊

theorem log_height_nonneg (p : ℤ) (a : Fin k → ℤ) :
    0 ≤ Real.log (coefficientHeight p a) := by
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ coefficientHeight p a from (by omega : 1 ≤ 2).trans (two_le_coefficientHeight p a))

theorem coefficient_norm_le (p : ℤ) (a : Fin k → ℤ) (r : Fin k) :
    ‖(a r : ℂ)‖ ≤ Real.exp (logarithmicWeight p a) := by
  have hH : (0 : ℝ) < coefficientHeight p a := by
    exact_mod_cast (show 0 < coefficientHeight p a from (by omega : 0 < 2).trans_le (two_le_coefficientHeight p a))
  calc
    _ = ((a r).natAbs : ℝ) := by simp
    _ ≤ (coefficientHeight p a : ℝ) := by exact_mod_cast natAbs_coefficient_le_height p a r
    _ = Real.exp (Real.log (coefficientHeight p a)) := (Real.exp_log hH).symm
    _ ≤ _ := Real.exp_le_exp.mpr (Nat.le_ceil _)

theorem error_form_le (α : Fin k → ℚ) (p : ℤ) (a : Fin k → ℤ) (ν : ℝ) (hν : 0 ≤ ν)
    (hbad : |linearForm α p a| ≤ (coefficientHeight p a : ℝ)^(-ν)) :
    |linearForm α p a| ≤ Real.exp (ν-ν*logarithmicWeight p a) := by
  have hH : (0 : ℝ) < coefficientHeight p a := by
    exact_mod_cast (show 0 < coefficientHeight p a from (by omega : 0 < 2).trans_le (two_le_coefficientHeight p a))
  apply hbad.trans
  rw [Real.rpow_def_of_pos hH]
  apply Real.exp_le_exp.mpr
  have hh := Nat.ceil_lt_add_one (log_height_nonneg p a)
  dsimp [logarithmicWeight]
  nlinarith [mul_le_mul_of_nonneg_left hh.le hν]

def omega (α : Fin k → ℚ) (r : Fin k) : ℂ := (Real.log (α r) : ℂ)

theorem exp_omega (α : Fin k → ℚ) (hα : ∀ r, 0 < α r) (r : Fin k) :
    Complex.exp (omega α r) = (α r : ℂ) := by
  rw [omega, ← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hα r)]
  norm_cast

theorem actual_error_le {m K : ℕ} (hK : 0 < K) (α : Fin k → ℚ)
    (p : Fin m → ℤ) (a : Fin m → Fin k → ℤ) (ν : ℝ) (hν : 0 ≤ ν)
    (hbad : ∀ i, |linearForm α (p i) (a i)| ≤ (coefficientHeight (p i) (a i) : ℝ)^(-ν))
    (j : Fin K) (i : Fin m) :
    ‖MultivariateRowTranslation.error a p (omega α) j.val i‖ ≤
      Real.exp ((Real.log K+ν)-ν*logarithmicWeight (p i) (a i)) := by
  have he : MultivariateRowTranslation.error a p (omega α) j.val i =
      -(j.val : ℂ)*(linearForm α (p i) (a i) : ℂ) := by
    simp [MultivariateRowTranslation.error, omega, linearForm]
  rw [he, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (K : ℝ)*Real.exp (ν-ν*logarithmicWeight (p i) (a i)) :=
      mul_le_mul (by exact_mod_cast j.isLt.le) (error_form_le α (p i) (a i) ν hν (hbad i))
        (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by
      rw [show Real.log K+ν-ν*(logarithmicWeight (p i) (a i) : ℝ) =
          Real.log K+(ν-ν*logarithmicWeight (p i) (a i)) by ring,
        Real.exp_add, Real.exp_log (by exact_mod_cast hK)]

/-- The failure hypothesis supplies genuine forms with arbitrarily large,
recursively separated logarithmic weights. -/
theorem exists_weighted_family (α : Fin k → ℚ) (hα : ∀ r, 0 < α r)
    (hind : MultiplicativelyIndependent α)
    (hlower : ∀ r : ℕ, 0 < r → r < k → ∀ β : Fin r → ℚ,
      (∀ s, 0 < β s) → MultiplicativelyIndependent β → EventualLinearFormLowerBound β)
    (ν : ℝ) (hν : (k : ℝ) < ν)
    (hfailure : ¬ ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ), H₀ ≤ coefficientHeight p a →
      (coefficientHeight p a : ℝ)^(-ν) ≤ |linearForm α p a|)
    (m : ℕ) (W G θ : ℝ) (hθ : 0 < θ) :
    ∃ (p : Fin m → ℤ) (a : Fin m → Fin k → ℤ),
      IntegerGeneralPosition a ∧ (∀ i, a i ≠ 0) ∧
      (∀ i, |linearForm α (p i) (a i)| < (coefficientHeight (p i) (a i) : ℝ)^(-ν)) ∧
      (∀ i, W < (logarithmicWeight (p i) (a i) : ℝ)) ∧
      ∀ i : Fin m, G*(∏ t : Fin i.val,
        (logarithmicWeight (p ⟨t.val,t.isLt.trans i.isLt⟩) (a ⟨t.val,t.isLt.trans i.isLt⟩) : ℝ)/θ) <
          (logarithmicWeight (p i) (a i) : ℝ)/θ := by
  let threshold := fun n (f : Fin n → GeneralPositionFamily.Form k) =>
    ⌈Real.exp (max W (θ*G*(∏ t, (logarithmicWeight (f t).1 (f t).2 : ℝ)/θ))+1)⌉₊
  obtain ⟨p,a,hgp,hne,hbad,hlarge,_⟩ :=
    GeneralPositionFamily.exists_exceptional_family α hα hind hlower ν hν hfailure threshold m
  have hweight (i : Fin m) :
      max W (θ*G*(∏ t : Fin i.val,
        (logarithmicWeight (p ⟨t.val,t.isLt.trans i.isLt⟩) (a ⟨t.val,t.isLt.trans i.isLt⟩) : ℝ)/θ)) <
          (logarithmicWeight (p i) (a i) : ℝ) := by
    have ht := hlarge i
    dsimp [threshold] at ht
    have he := (Nat.le_ceil (Real.exp (max W (θ*G*(∏ t : Fin i.val,
      (logarithmicWeight (p ⟨t.val,t.isLt.trans i.isLt⟩) (a ⟨t.val,t.isLt.trans i.isLt⟩) : ℝ)/θ))+1))).trans
      (Nat.cast_le.mpr ht)
    have hl := Real.log_le_log (Real.exp_pos _) he
    rw [Real.log_exp] at hl
    have hc := Nat.le_ceil (Real.log (coefficientHeight (p i) (a i)))
    change _ ≤ (logarithmicWeight (p i) (a i) : ℝ) at hc
    linarith
  refine ⟨p,a,hgp,hne,hbad,fun i => (le_max_left _ _).trans_lt (hweight i),fun i => ?_⟩
  apply (lt_div_iff₀ hθ).mpr
  have hh := (le_max_right _ _).trans_lt (hweight i)
  convert hh using 1 <;> ring

end
end GeneralizedLogarithms.MultivariateExceptionalWeights

/-- info: 'GeneralizedLogarithms.MultivariateExceptionalWeights.exists_weighted_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateExceptionalWeights.exists_weighted_family

/-- info: 'GeneralizedLogarithms.MultivariateExceptionalWeights.actual_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateExceptionalWeights.actual_error_le
