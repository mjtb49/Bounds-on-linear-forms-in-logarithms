import GeneralizedLogarithms.MultivariateParameters
import GeneralizedLogarithms.MultivariateModeCapacity
import GeneralizedLogarithms.LongitudinalAsymptotics
import LogIrrationalityMeasure.Approximation.Arithmetic

/-! Decay of the dimension-dependent arithmetic and Taylor-capacity costs. -/

namespace GeneralizedLogarithms.MultivariateDecayParameters

noncomputable section
open scoped BigOperators Topology
open Filter LogIrrationalityMeasure.LogExponent

theorem tendsto_choose_mul_pow (k : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun m : ℕ => ((k+m).choose k : ℝ)*q^m) atTop (𝓝 0) := by
  have hh := (tendsto_pow_const_mul_const_pow_of_lt_one k hq hq1).const_mul ((2 : ℝ)^k)
  simp only [mul_zero] at hh
  apply squeeze_zero' (Eventually.of_forall (fun m => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq _))) _ hh
  filter_upwards [eventually_ge_atTop k] with m hm
  have hc : ((k+m).choose k : ℝ) ≤ ((2 : ℝ)*m)^k := by
    exact_mod_cast (Nat.choose_le_pow (k+m) k).trans (Nat.pow_le_pow_left (by omega) k)
  calc
    _ ≤ ((2 : ℝ)*m)^k*q^m := mul_le_mul_of_nonneg_right hc (pow_nonneg hq _)
    _ = _ := by rw [mul_pow]; ring

theorem tendsto_capacity_ratio (k : ℕ) (B C D θ A S : ℝ)
    (hB : 0 < B) (hC : 1 < C) (hD : 0 < D) (hθ : 0 < θ) (hA : 0 < A)
    (hgap : D^k < B^k*C*θ/A) :
    Tendsto (fun m : ℕ => ((k+m).choose k : ℝ)*((D/B)^m)^k*A^m*S^k /
      ((⌊C^m⌋₊ : ℝ)*θ^m)) atTop (𝓝 0) := by
  let q := D^k*A/(B^k*C*θ)
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hden : 0 < B^k*C*θ := mul_pos (mul_pos (pow_pos hB k) hC0) hθ
  have hq : 0 ≤ q := (div_pos (mul_pos (pow_pos hD k) hA) hden).le
  have hq1 : q < 1 := (div_lt_one hden).mpr ((lt_div_iff₀ hA).mp hgap)
  have hf := (tendsto_nat_floor_div_atTop (R := ℝ)).comp (tendsto_pow_atTop_atTop_of_one_lt hC)
  have hi := hf.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hh := ((tendsto_choose_mul_pow k q hq hq1).mul_const (S^k)).mul hi
  simp only [zero_mul, inv_one] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun m => by
    dsimp [q]
    simp only [Function.comp_apply, inv_div, div_pow, mul_pow, ← pow_mul]
    rw [Nat.mul_comm m k]
    field_simp
    <;> ring)

theorem tendsto_center_cost (B C L : ℝ) (hB : 0 < B) (hC : 0 ≤ C) (hBC : C*B < 1) :
    Tendsto (fun m : ℕ => (⌊C^m⌋₊ : ℝ)*L/(1/B)^m) atTop (𝓝 0) := by
  have hf : Tendsto (fun m : ℕ => (⌊C^m⌋₊ : ℝ)*B^m) atTop (𝓝 0) := by
    apply squeeze_zero (fun m => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB.le _))
      (fun m => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hC hB.le) hBC)
    calc
      _ ≤ C^m*B^m := mul_le_mul_of_nonneg_right (Nat.floor_le (pow_nonneg hC m)) (pow_nonneg hB.le _)
      _ = _ := (mul_pow _ _ _).symm
  convert hf.mul_const L using 1
  · funext m
    simp only [one_div, inv_pow, div_inv_eq_mul]
    ring
  · simp

theorem tendsto_cutoff_cost (B D L : ℝ) (hB : 0 < B) (hBD : B < D) :
    Tendsto (fun m : ℕ => L*m/(D/B)^m) atTop (𝓝 0) := by
  have hD := hB.trans hBD
  have hh := (tendsto_pow_const_mul_const_pow_of_lt_one 1
    (div_nonneg hB.le hD.le) ((div_lt_one hD).mpr hBD)).const_mul L
  simp only [pow_one, mul_zero] at hh
  convert hh using 1
  funext m
  rw [div_pow, div_pow]
  field_simp

theorem tendsto_longitudinal_cost (B D L : ℝ) (hB : 0 < B) (hBD : B < D) :
    Tendsto (fun m : ℕ => L/(D/B)^m) atTop (𝓝 0) := by
  have hD := hB.trans hBD
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (div_nonneg hB.le hD.le) ((div_lt_one hD).mpr hBD)).const_mul L
  simp only [mul_zero] at hh
  convert hh using 1
  funext m
  rw [div_pow, div_pow]
  field_simp

end
end GeneralizedLogarithms.MultivariateDecayParameters

/-- info: 'GeneralizedLogarithms.MultivariateDecayParameters.tendsto_capacity_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateDecayParameters.tendsto_capacity_ratio

/-- info: 'GeneralizedLogarithms.MultivariateDecayParameters.tendsto_cutoff_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateDecayParameters.tendsto_cutoff_cost
