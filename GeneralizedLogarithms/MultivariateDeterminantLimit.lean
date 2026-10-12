import GeneralizedLogarithms.MultivariateAnalyticSetup
import LogIrrationalityMeasure.Analysis.TranslationCountLimit
import LogIrrationalityMeasure.Analysis.CollisionExponential

/-! The counting losses vanish after division by the product of row count
and height. All bounds concern the actual determinant estimate. -/

namespace GeneralizedLogarithms.MultivariateDeterminantLimit

noncomputable section
open scoped BigOperators Topology
open Filter LogIrrationalityMeasure.LogExponent
open MultivariateAnalyticSetup MultivariateModeCapacity

theorem tendsto_termCount_normalized (k m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => (termCount k m v H : ℝ)/H^(2*m+k)) atTop (𝓝 ((1/v)^k)) := by
  have h₁ : Tendsto (fun H : ℝ => ((⌊H⌋₊+1 : ℕ) : ℝ)/H) atTop (𝓝 1) := by
    simpa only [one_mul] using tendsto_natFloor_mul_add_one_div (show (0 : ℝ)<1 by norm_num)
  have h₂ : Tendsto (fun H : ℝ => ((⌊H/v⌋₊+1 : ℕ) : ℝ)/H) atTop (𝓝 (1/v)) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using
      tendsto_natFloor_mul_add_one_div (div_pos zero_lt_one hv)
  have hh := (h₁.pow (2*m)).mul (h₂.pow k)
  simp only [one_pow, one_mul] at hh
  convert hh using 1
  funext H
  simp only [termCount, Nat.cast_mul, Nat.cast_pow, div_pow, div_mul_div_comm, pow_add]

def overhead (k m : ℕ) (v : ℝ) (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log (termCount k m v H : ℝ)+Real.log M+k*Real.log 4)/H

theorem tendsto_overhead (k m K : ℕ) (hK : 0 < K)
    (v₀ θ : ℚ) (w : Fin m → ℚ) (hv : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : ℝ => overhead k m v₀ (rowCount (k := k) K v₀ θ w H) H) atTop (𝓝 0) := by
  have hvR : (0 : ℝ) < v₀ := by exact_mod_cast hv
  have hq := tendsto_log_div_of_normalized_pow (tendsto_termCount_normalized k m hvR)
    (pow_pos (div_pos zero_lt_one hvR) k)
  have hρ : 0 < rowDensity (k := k) K v₀ θ w := by
    unfold rowDensity
    apply div_pos
    · exact mul_pos (by exact_mod_cast hK) (pow_pos (by exact_mod_cast hθ) m)
    · exact mul_pos (mul_pos (by exact_mod_cast Nat.factorial_pos (k+m)) (pow_pos hvR k))
        (Finset.prod_pos (fun i _ => by exact_mod_cast hw i))
  have hr := tendsto_log_div_of_normalized_pow (tendsto_rowCount K v₀ θ w hv hθ hw) hρ
  have hh := (hq.add hr).add (tendsto_id.const_div_atTop ((k : ℝ)*Real.log 4))
  simpa only [overhead, add_div, zero_add, id_eq] using hh

theorem normalized_log_upper {k m M : ℕ} (v H c x : ℝ) (hM : 0 < M)
    (hH : 0 < H) (hx : 0 < x)
    (hb : x ≤ (termCount k m v H : ℝ)^M*M.factorial*
      Real.exp (-(M : ℝ)*H*c+(k*M : ℕ)*Real.log 4)) :
    Real.log x/((M : ℝ)*H) ≤ -c+overhead k m v M H := by
  have hQ : (0 : ℝ) < termCount k m v H := by
    exact_mod_cast (show 0 < termCount k m v H by unfold termCount; positivity)
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hfac := Collision.factorial_le_exp_card_log M
  have he : x ≤ Real.exp ((M : ℝ)*H*(-c+overhead k m v M H)) := by
    apply hb.trans
    calc
      _ ≤ (termCount k m v H : ℝ)^M*Real.exp ((M : ℝ)*Real.log M)*
          Real.exp (-(M : ℝ)*H*c+(k*M : ℕ)*Real.log 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac (by positivity)) (Real.exp_pos _).le
      _ = _ := by
        rw [show (termCount k m v H : ℝ)^M =
            Real.exp ((M : ℝ)*Real.log (termCount k m v H : ℝ)) by
          rw [Real.exp_nat_mul, Real.exp_log hQ], ← Real.exp_add, ← Real.exp_add]
        congr 1
        simp only [overhead, Nat.cast_mul]
        field_simp
        <;> ring
  have hh := Real.log_le_log hx he
  rw [Real.log_exp] at hh
  apply (div_le_iff₀ (mul_pos hMR hH)).mpr
  convert hh using 1 <;> ring

end
end GeneralizedLogarithms.MultivariateDeterminantLimit

/-- info: 'GeneralizedLogarithms.MultivariateDeterminantLimit.tendsto_overhead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateDeterminantLimit.tendsto_overhead

/-- info: 'GeneralizedLogarithms.MultivariateDeterminantLimit.normalized_log_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateDeterminantLimit.normalized_log_upper
