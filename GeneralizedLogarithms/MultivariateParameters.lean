import LogIrrationalityMeasure.Approximation.Parameters
import LogIrrationalityMeasure.Approximation.Sigma

/-!
# Rational parameters for the multivariate contradiction

The nonempty parameter intervals are consequences of `ν > k`. The choices
proceed through `b`, a small `δ`, then `B`, `C`, `D`, and finally `σ`.
The power inequality near `δ = 0` follows from continuity of a finite
geometric sum, without any asymptotic arithmetic estimate as a hypothesis.
-/

namespace GeneralizedLogarithms.MultivariateParameters

noncomputable section
open scoped BigOperators

/-- A positive-degree power has rational arguments in every positive target
interval. The argument itself, rather than its power, is rational. -/
theorem exists_rational_power_between (k : ℕ) (hk : 1 ≤ k)
    (L U : ℝ) (hL : 0 ≤ L) (hLU : L < U) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ L < (q : ℝ)^k ∧ (q : ℝ)^k < U := by
  have hk0 : k ≠ 0 := by omega
  let l := L ^ ((k : ℝ)⁻¹)
  let u := U ^ ((k : ℝ)⁻¹)
  have hl0 : 0 ≤ l := Real.rpow_nonneg hL _
  have hu0 : 0 < u := Real.rpow_pos_of_pos (hL.trans_lt hLU) _
  have hlpow : l^k = L := Real.rpow_inv_natCast_pow hL hk0
  have hupow : u^k = U := Real.rpow_inv_natCast_pow (hL.trans hLU.le) hk0
  have hlu : l < u := lt_of_pow_lt_pow_left₀ k hu0.le (by rwa [hlpow, hupow])
  obtain ⟨q, hlq, hqu⟩ := exists_rat_btwn hlu
  refine ⟨q, hl0.trans_lt hlq, ?_, ?_⟩
  · rw [← hlpow]
    exact pow_lt_pow_left₀ hlq hl0 hk0
  · rw [← hupow]
    exact pow_lt_pow_left₀ hqu (hl0.trans hlq.le) hk0

/-- The strict first-order inequality at zero persists for a small positive
rational `δ`; the geometric-sum identity gives the desired power comparison. -/
theorem exists_small_delta (k : ℕ) (b : ℚ)
    (hb : (k : ℝ) < ((k : ℝ) + 1) * b) :
    ∃ δ : ℚ, 0 < (δ : ℝ) ∧ (δ : ℝ) < 1 ∧
      (1 - (b : ℝ) * δ)^(k+1) < (1 - (δ : ℝ))^k := by
  let g (x : ℝ) := (b : ℝ) * ∑ i ∈ Finset.range (k+1), (1 - (b : ℝ)*x)^i -
    ∑ i ∈ Finset.range k, (1-x)^i
  have hg0 : 0 < g 0 := by
    simp only [g, mul_zero, sub_zero, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hopen : IsOpen {x : ℝ | 0 < g x} := isOpen_lt continuous_const (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hg0
  obtain ⟨δ, hδ, hδtop⟩ := exists_rat_btwn (lt_min hε (show (0 : ℝ) < 1 by norm_num))
  have hgδ : 0 < g δ := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδ]
    exact hδtop.trans_le (min_le_left _ _))
  have hA := geom_sum_mul_neg (1 - (b : ℝ) * δ) (k+1)
  have hθ := geom_sum_mul_neg (1 - (δ : ℝ)) k
  have hprod := mul_pos hδ hgδ
  dsimp only [g] at hprod
  refine ⟨δ, hδ, hδtop.trans_le (min_le_right _ _), ?_⟩
  nlinarith [hA, hθ]

/-- The three geometric parameters are selected from intervals whose
nonemptiness is proved from the longitudinal power inequality. -/
theorem exists_rational_geometry_parameters (k : ℕ) (hk : 1 ≤ k)
    (θ A : ℚ) (hθ : 0 < (θ : ℝ)) (hθA : (θ : ℝ) < A) (hA1 : (A : ℝ) < 1)
    (hpower : (A : ℝ)^(k+1) < (θ : ℝ)^k) :
    ∃ B C D : ℚ, 0 < (B : ℝ) ∧ 1 < (C : ℝ) ∧
      (A : ℝ) < (B : ℝ)^k ∧ (A : ℝ) < (C : ℝ)*θ ∧ (C : ℝ)*B < 1 ∧
      (B : ℝ) < D ∧ (D : ℝ) < 1 ∧
      (C : ℝ)*θ < (D : ℝ)^k ∧
      (D : ℝ)^k < (B : ℝ)^k * C * θ / A := by
  have hk0 : k ≠ 0 := by omega
  have hA : 0 < (A : ℝ) := hθ.trans hθA
  have hupper : (A : ℝ) < ((θ : ℝ) / A)^k := by
    rw [div_pow]
    apply (lt_div_iff₀ (pow_pos hA k)).mpr
    simpa only [pow_succ, mul_comm] using hpower
  obtain ⟨B, hB, hAB, hBupper⟩ := exists_rational_power_between k hk A (((θ : ℝ)/A)^k) hA.le hupper
  have hBθA : (B : ℝ) < (θ : ℝ)/A :=
    lt_of_pow_lt_pow_left₀ k (div_pos hθ hA).le hBupper
  have hB1 : (B : ℝ) < 1 := hBθA.trans ((div_lt_one hA).mpr hθA)
  have hBA : (A : ℝ) < B := hAB.trans_le (pow_le_of_le_one hB.le hB1.le hk0)
  have hCinterval : (A : ℝ)/θ < 1/(B : ℝ) := by
    apply (div_lt_div_iff₀ hθ hB).mpr
    have hh := (lt_div_iff₀ hA).mp hBθA
    nlinarith
  obtain ⟨C, hClo, hChi⟩ := exists_rat_btwn hCinterval
  have hC1 : (1 : ℝ) < C := ((one_lt_div hθ).mpr hθA).trans hClo
  have hC : 0 < (C : ℝ) := zero_lt_one.trans hC1
  have hACθ : (A : ℝ) < (C : ℝ)*θ := (div_lt_iff₀ hθ).mp hClo
  have hCB : (C : ℝ)*B < 1 := (lt_div_iff₀ hB).mp hChi
  have hCθ : 0 < (C : ℝ)*θ := mul_pos hC hθ
  have hCθ1 : (C : ℝ)*θ < 1 := by
    exact (mul_lt_mul_of_pos_left (hθA.trans hBA) hC).trans hCB
  have hBk : 0 < (B : ℝ)^k := pow_pos hB k
  have hBk1 : (B : ℝ)^k < 1 := pow_lt_one₀ hB.le hB1 hk0
  have htopB : (B : ℝ)^k < (B : ℝ)^k*C*θ/A := by
    apply (lt_div_iff₀ hA).mpr
    nlinarith [mul_lt_mul_of_pos_left hACθ hBk]
  have htopC : (C : ℝ)*θ < (B : ℝ)^k*C*θ/A := by
    apply (lt_div_iff₀ hA).mpr
    nlinarith [mul_lt_mul_of_pos_right hAB hCθ]
  have hinterval : max ((B : ℝ)^k) ((C : ℝ)*θ) <
      min (1 : ℝ) ((B : ℝ)^k*C*θ/A) :=
    max_lt (lt_min hBk1 htopB) (lt_min hCθ1 htopC)
  obtain ⟨D, hD, hDlo, hDhi⟩ := exists_rational_power_between k hk _ _
    ((hBk.le).trans (le_max_left _ _)) hinterval
  have hBD : (B : ℝ) < D := lt_of_pow_lt_pow_left₀ k hD.le
    ((le_max_left _ _).trans_lt hDlo)
  have hD1 : (D : ℝ) < 1 := lt_of_pow_lt_pow_left₀ k zero_le_one (by
    simpa only [one_pow] using hDhi.trans_le (min_le_left _ _))
  exact ⟨B, C, D, hB, hC1, hAB, hACθ, hCB, hBD, hD1,
    (le_max_right _ _).trans_lt hDlo, hDhi.trans_le (min_le_right _ _)⟩

structure Parameters (k : ℕ) (ν : ℝ) where
  b : ℚ
  δ : ℚ
  θ : ℚ
  A : ℚ
  B : ℚ
  C : ℚ
  D : ℚ
  σ : ℚ
  η : ℝ
  b_lower : (k : ℝ)/((k : ℝ)+1) < b
  b_upper : (b : ℝ) < ν/(ν+1)
  delta_pos : 0 < (δ : ℝ)
  delta_lt_one : (δ : ℝ) < 1
  theta_eq : θ = 1-δ
  A_eq : A = 1-b*δ
  theta_pos : 0 < (θ : ℝ)
  theta_lt_A : (θ : ℝ) < A
  A_lt_one : (A : ℝ) < 1
  longitudinal_power : (A : ℝ)^(k+1) < (θ : ℝ)^k
  eta_pos : 0 < η
  eta_lt_one : η < 1
  arithmetic_gap : 0 < (ν+1)*(A : ℝ)*(1-η)-1-ν*θ
  B_pos : 0 < (B : ℝ)
  one_lt_C : 1 < (C : ℝ)
  A_lt_B_pow : (A : ℝ) < (B : ℝ)^k
  A_lt_C_theta : (A : ℝ) < (C : ℝ)*θ
  CB_lt_one : (C : ℝ)*B < 1
  B_lt_D : (B : ℝ) < D
  D_lt_one : (D : ℝ) < 1
  C_theta_lt_D_pow : (C : ℝ)*θ < (D : ℝ)^k
  D_pow_lt_collision_scale : (D : ℝ)^k < (B : ℝ)^k*C*θ/A
  sigma_pos : 0 < (σ : ℝ)
  volume_margin : (1+3*(σ : ℝ))*((C : ℝ)*θ/(D : ℝ)^k) < 1
  fibre_discount : (1+(σ : ℝ))*θ < 1

/-- All proposed fixed rational parameters exist in their prescribed choice
order, with a real positive arithmetic slack. -/
theorem exists_parameters (k : ℕ) (hk : 1 ≤ k) (ν : ℝ) (hν : (k : ℝ) < ν) :
    Nonempty (Parameters k ν) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : 0 < (k : ℝ)+1 := by positivity
  have hν1 : 0 < ν+1 := by linarith
  have hinterval : (k : ℝ)/((k : ℝ)+1) < ν/(ν+1) := by
    apply (div_lt_div_iff₀ hk1 hν1).mpr
    nlinarith
  obtain ⟨b, hbl, hbu⟩ := exists_rat_btwn hinterval
  have hb0 : 0 < (b : ℝ) := (div_pos (by linarith) hk1).trans hbl
  have hb1 : (b : ℝ) < 1 := hbu.trans ((div_lt_one hν1).mpr (by linarith))
  have hbderiv : (k : ℝ) < ((k : ℝ)+1)*b := by
    have hh := (div_lt_iff₀ hk1).mp hbl
    nlinarith
  obtain ⟨δ, hδ, hδ1, hpower⟩ := exists_small_delta k b hbderiv
  let θ : ℚ := 1-δ
  let A : ℚ := 1-b*δ
  have hθeq : (θ : ℝ) = 1-(δ : ℝ) := by simp [θ]
  have hAeq : (A : ℝ) = 1-(b : ℝ)*δ := by simp [A]
  have hθ : 0 < (θ : ℝ) := by rw [hθeq]; linarith
  have hθA : (θ : ℝ) < A := by
    rw [hθeq, hAeq]
    nlinarith [mul_pos (sub_pos.mpr hb1) hδ]
  have hA1 : (A : ℝ) < 1 := by rw [hAeq]; nlinarith [mul_pos hb0 hδ]
  have hpow : (A : ℝ)^(k+1) < (θ : ℝ)^k := by rwa [hAeq, hθeq]
  have hgap : 1-(θ : ℝ) < (ν+1)*((A : ℝ)-θ) := by
    have hνb := (lt_div_iff₀ hν1).mp hbu
    rw [hθeq, hAeq]
    nlinarith [mul_pos hδ (sub_pos.mpr hνb)]
  obtain ⟨η, hη, hη1, hgapη⟩ :=
    LogIrrationalityMeasure.LogExponent.exists_eta_preserving_exponent_gap
      (ν+1) θ A (by linarith) (hθ.trans hθA) hgap
  have hgap' : 0 < (ν+1)*(A : ℝ)*(1-η)-1-ν*θ := by nlinarith [hgapη]
  obtain ⟨B, C, D, hB, hC1, hAB, hACθ, hCB, hBD, hD1, hCθD, hDtop⟩ :=
    exists_rational_geometry_parameters k hk θ A hθ hθA hA1 hpow
  have hD : 0 < (D : ℝ) := hB.trans hBD
  have hvol : (C : ℝ)*θ/(D : ℝ)^k < 1 :=
    (div_lt_one (pow_pos hD k)).mpr hCθD
  obtain ⟨σ, hσ, hσvol, _, hσθ⟩ :=
    LogIrrationalityMeasure.LogExponent.exists_small_rational_sigma 0
      ((C : ℝ)*θ/(D : ℝ)^k) 0 θ hvol (by norm_num) (hθA.trans hA1)
  refine ⟨⟨b, δ, θ, A, B, C, D, σ, η, hbl, hbu, hδ, hδ1, rfl, rfl,
    hθ, hθA, hA1, hpow, hη, hη1, hgap', hB, hC1, hAB, hACθ, hCB, hBD,
    hD1, hCθD, hDtop, hσ, ?_, hσθ⟩⟩
  simpa only [Nat.zero_add, pow_one] using hσvol

end
end GeneralizedLogarithms.MultivariateParameters

/-- info: 'GeneralizedLogarithms.MultivariateParameters.exists_rational_geometry_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateParameters.exists_rational_geometry_parameters

/-- info: 'GeneralizedLogarithms.MultivariateParameters.exists_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateParameters.exists_parameters
