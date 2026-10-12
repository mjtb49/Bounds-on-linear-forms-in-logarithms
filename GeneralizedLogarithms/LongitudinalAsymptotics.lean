import GeneralizedLogarithms.LongitudinalComparison
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Eventual longitudinal gaps with fixed logarithmic rank

The checked comparison factor retains codimension at most `2*k-1`. With
`epsilon = sigma / (k+m+1)`, it is bounded by a polynomial of fixed degree in
`m`. Consequently the proposed exponentially increasing longitudinal ratio
eventually gives every required small-rank gap simultaneously.
-/

namespace GeneralizedLogarithms.LongitudinalAsymptotics

open Filter Topology

/-- A fixed-degree polynomial bounds all codimension-dependent comparison
factors. The coefficient depends on `k`, `b` and `sigma`, not on `m` or `d`. -/
theorem comparison_factor_le_polynomial (k b m d : ℕ)
    (hb : 1 ≤ b) (hm : 1 ≤ m) (hd : d ≤ b)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    (d : ℝ)^d / (sigma / ((k : ℝ) + m + 1))^d ≤
      (b : ℝ)^b * (1 + ((k : ℝ) + 2) / sigma)^b * (m : ℝ)^b := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hL : 0 ≤ (k : ℝ) + m + 1 := by positivity
  have hbound := rectangular_factor_le_fixed_degree d b
    ((k : ℝ) + m + 1) sigma hb hd hL hsigma
  have hbase : 1 + ((k : ℝ) + m + 1) / sigma ≤
      (1 + ((k : ℝ) + 2) / sigma) * m := by
    apply (le_of_mul_le_mul_right ?_ hsigma)
    have hh : (k : ℝ) + m + 1 ≤ ((k : ℝ) + 2) * m := by nlinarith
    calc
      (1 + ((k : ℝ) + m + 1) / sigma) * sigma =
          sigma + ((k : ℝ) + m + 1) := by field_simp
      _ ≤ sigma * m + ((k : ℝ) + 2) * m := by nlinarith
      _ = ((1 + ((k : ℝ) + 2) / sigma) * m) * sigma := by field_simp
  calc
    _ = (d : ℝ)^d * (((k : ℝ) + m + 1) / sigma)^d := by
      rw [div_pow, div_div_eq_mul_div, mul_div_assoc, div_pow]
    _ ≤ (b : ℝ)^b * (1 + ((k : ℝ) + m + 1) / sigma)^b := hbound
    _ ≤ (b : ℝ)^b * ((1 + ((k : ℝ) + 2) / sigma) * m)^b :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase b) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- All the longitudinal gaps required by the multivariate curve argument hold
eventually, uniformly in the small-rank indices `r` and `d`. -/
theorem eventually_longitudinal_gap (k : ℕ) (hk : 1 ≤ k)
    (theta D sigma : ℝ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hD : 0 < D) (hD1 : D < 1) (hsigma : 0 < sigma) :
    ∀ᶠ m : ℕ in atTop, ∀ r d : ℕ, r < k → 1 ≤ d-r → d-r ≤ k → d ≤ 2*k-1 →
      (d : ℝ)^d / (sigma / ((k : ℝ) + m + 1))^d <
        theta^r * ((1 / D)^m)^(d-r) := by
  let b : ℕ := 2*k-1
  let A : ℝ := (b : ℝ)^b * (1 + ((k : ℝ) + 2) / sigma)^b
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hlim : Tendsto (fun m : ℕ => A * ((m : ℝ)^b * D^m)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one b hD.le hD1).const_mul A
  have hsmall := hlim.eventually (gt_mem_nhds (pow_pos htheta (k-1)))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with m hm hm1
  intro r d hr hdr _ hd
  have hcompare := comparison_factor_le_polynomial k b m d hb hm1 hd sigma hsigma
  have hscaled : ((d : ℝ)^d / (sigma / ((k : ℝ) + m + 1))^d) * D^m <
      theta^(k-1) := by
    calc
      _ ≤ (A * (m : ℝ)^b) * D^m :=
        mul_le_mul_of_nonneg_right hcompare (pow_nonneg hD.le m)
      _ = A * ((m : ℝ)^b * D^m) := by ring
      _ < _ := hm
  have hfirst : (d : ℝ)^d / (sigma / ((k : ℝ) + m + 1))^d <
      theta^(k-1) * (1 / D)^m := by
    have hh := (lt_div_iff₀ (pow_pos hD m)).mpr hscaled
    simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using hh
  have hrle : r ≤ k-1 := by omega
  have hthetaPow : theta^(k-1) ≤ theta^r :=
    pow_le_pow_of_le_one htheta.le htheta1 hrle
  have hratio : 1 ≤ (1 / D)^m :=
    one_le_pow₀ ((one_le_div hD).mpr hD1.le)
  have hratioPow : (1 / D)^m ≤ ((1 / D)^m)^(d-r) := by
    simpa only [pow_one] using pow_le_pow_right₀ hratio hdr
  exact hfirst.trans_le (mul_le_mul hthetaPow hratioPow
    (le_trans zero_le_one hratio) (pow_nonneg htheta.le r))

/-- The proposed center count `floor (C^m)` and exponential longitudinal ratio
satisfy the high-jet volume inequality eventually. The scalar `scale` is
instantiated with `1+3*sigma` in the curve argument. -/
theorem eventually_volume_inequality (k : ℕ) (C theta D scale : ℝ)
    (hC : 0 ≤ C) (htheta : 0 ≤ theta) (hD : 0 < D) (hscale : 0 ≤ scale)
    (hmargin : scale * C * theta / D^k < 1) :
    ∀ᶠ m : ℕ in atTop,
      (⌊C^m⌋₊ : ℝ) * scale^(k+m) * ((1/D)^m)^k * theta^m < 1 := by
  let q : ℝ := scale * C * theta / D^k
  have hq : 0 ≤ q := div_nonneg (mul_nonneg (mul_nonneg hscale hC) htheta)
    (pow_nonneg hD.le k)
  have hlim : Tendsto (fun m : ℕ => scale^k * q^m) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq hmargin).const_mul (scale^k)
  filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one)] with m hm
  have hfloor : (⌊C^m⌋₊ : ℝ) ≤ C^m := Nat.floor_le (pow_nonneg hC m)
  calc
    _ ≤ C^m * scale^(k+m) * ((1/D)^m)^k * theta^m := by
      gcongr
    _ = scale^k * q^m := by
      dsimp [q]
      simp only [pow_add, div_pow, mul_pow, one_pow, ← pow_mul]
      rw [Nat.mul_comm m k]
      ring
    _ < 1 := hm

end GeneralizedLogarithms.LongitudinalAsymptotics

/-- info: 'GeneralizedLogarithms.LongitudinalAsymptotics.comparison_factor_le_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.LongitudinalAsymptotics.comparison_factor_le_polynomial

/-- info: 'GeneralizedLogarithms.LongitudinalAsymptotics.eventually_longitudinal_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.LongitudinalAsymptotics.eventually_longitudinal_gap

/-- info: 'GeneralizedLogarithms.LongitudinalAsymptotics.eventually_volume_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.LongitudinalAsymptotics.eventually_volume_inequality
