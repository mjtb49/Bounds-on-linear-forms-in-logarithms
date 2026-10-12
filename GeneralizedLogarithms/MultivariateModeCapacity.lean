import GeneralizedLogarithms.Collision
import LogIrrationalityMeasure.Polynomials.AuxiliaryPolynomial

/-!
# Asymptotic capacity of complete multivariate Taylor modes

The low-mode set is a product of a transverse weighted simplex and a strict
longitudinal simplex. Its exact leading coefficient, compared with the full
jet-row count, supplies the capacity hypothesis in the checked collision lemma.
This is a counting result; analytic determinant expansion is a separate step.
-/

namespace GeneralizedLogarithms.MultivariateModeCapacity

noncomputable section
open scoped BigOperators
open Filter Topology
open LogIrrationalityMeasure.LogExponent

variable {k m : ℕ}

def lowModes (w : Fin m → ℚ) (A S H : ℝ) :
    Finset ((Fin m → ℕ) × (Fin k → ℕ)) :=
  (realWeightedSimplex (fun i => (w i : ℝ)) (A * H)) ×ˢ
    (strictWeightedSimplex (fun _ : Fin k => (1 : ℝ)) (S * H))

theorem mem_lowModes (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    (A S H : ℝ) (γ : Fin m → ℕ) (d : Fin k → ℕ) :
    (γ, d) ∈ lowModes w A S H ↔
      (∑ i, (w i : ℝ) * γ i) ≤ A * H ∧ (∑ r, (d r : ℝ)) < S * H := by
  rw [lowModes, Finset.mem_product, mem_realWeightedSimplex
    (fun i => show (0 : ℝ) < w i by exact_mod_cast hw i),
    mem_strictWeightedSimplex (fun _ => zero_lt_one)]
  simp only [one_mul]

def rowWeights (v₀ θ : ℚ) (w : Fin m → ℚ) : Fin (k + m) → ℚ :=
  Fin.addCases (fun _ => v₀) (fun i => w i / θ)

def rowCount (K : ℕ) (v₀ θ : ℚ) (w : Fin m → ℚ) (H : ℝ) : ℕ :=
  K * (strictWeightedSimplex (fun i => (rowWeights (k := k) v₀ θ w i : ℝ)) H).card

def capacityDensity (w : Fin m → ℚ) (A S : ℝ) : ℝ :=
  A ^ m * S ^ k / ((m.factorial : ℝ) * k.factorial * ∏ i, (w i : ℝ))

def rowDensity (K : ℕ) (v₀ θ : ℚ) (w : Fin m → ℚ) : ℝ :=
  (K : ℝ) * (θ : ℝ) ^ m /
    (((k + m).factorial : ℝ) * (v₀ : ℝ) ^ k * ∏ i, (w i : ℝ))

theorem tendsto_card_realWeightedSimplex_scale {n : ℕ} (w : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H : ℝ =>
      ((realWeightedSimplex (fun i => (w i : ℝ)) (a * H)).card : ℝ) / H ^ n)
      atTop (𝓝 (a ^ n / ((n.factorial : ℝ) * ∏ i, (w i : ℝ)))) := by
  have ht : Tendsto (fun H : ℝ => a * H) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_id
  have h := ((tendsto_card_realWeightedSimplex_rational w hw).comp ht).mul_const (a ^ n)
  have heq : 1 / ((n.factorial : ℝ) * ∏ i, (w i : ℝ)) * a ^ n =
      a ^ n / ((n.factorial : ℝ) * ∏ i, (w i : ℝ)) := by ring
  rw [heq] at h
  apply h.congr'
  exact Eventually.of_forall (fun H => by
    simp only [Function.comp_apply, mul_pow]
    field_simp)

theorem tendsto_lowModes_card (w : Fin m → ℚ) (hw : ∀ i, 0 < w i)
    (A S : ℝ) (hA : 0 < A) (hS : 0 < S) :
    Tendsto (fun H : ℝ => ((lowModes (k := k) w A S H).card : ℝ) / H ^ (k + m))
      atTop (𝓝 (capacityDensity (k := k) w A S)) := by
  have hleft := tendsto_card_realWeightedSimplex_scale w hw hA
  have hright := tendsto_card_strictWeightedSimplex_scale
    (fun _ : Fin k => (1 : ℚ)) (fun _ => zero_lt_one) hS
  simp only [Rat.cast_one, Finset.prod_const_one, mul_one] at hright
  have h := hright.mul hleft
  have heq : (S ^ k / (k.factorial : ℝ)) *
      (A ^ m / ((m.factorial : ℝ) * ∏ i, (w i : ℝ))) =
        capacityDensity (k := k) w A S := by dsimp [capacityDensity]; ring
  rw [heq] at h
  apply h.congr'
  exact Eventually.of_forall (fun H => by
    simp only [lowModes, Finset.card_product, Nat.cast_mul, pow_add]
    ring)

theorem rowWeights_pos (v₀ θ : ℚ) (w : Fin m → ℚ)
    (hv₀ : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) :
    ∀ j, 0 < rowWeights (k := k) v₀ θ w j := by
  intro j
  refine Fin.addCases (fun _ => ?_) (fun i => ?_) j
  · simpa [rowWeights] using hv₀
  · simpa [rowWeights] using div_pos (hw i) hθ

theorem prod_rowWeights (v₀ θ : ℚ) (w : Fin m → ℚ) :
    (∏ j, (rowWeights (k := k) v₀ θ w j : ℝ)) =
      (v₀ : ℝ) ^ k * (∏ i, (w i : ℝ)) / (θ : ℝ) ^ m := by
  rw [Fin.prod_univ_add]
  simp [rowWeights, Finset.prod_div_distrib, mul_div_assoc]

theorem tendsto_rowCount (K : ℕ) (v₀ θ : ℚ) (w : Fin m → ℚ)
    (hv₀ : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : ℝ => (rowCount (k := k) K v₀ θ w H : ℝ) / H ^ (k + m))
      atTop (𝓝 (rowDensity (k := k) K v₀ θ w)) := by
  have h := (tendsto_card_strictWeightedSimplex_rational
    (rowWeights (k := k) v₀ θ w) (rowWeights_pos v₀ θ w hv₀ hθ hw)).const_mul (K : ℝ)
  have heq : (K : ℝ) * (1 / (((k + m).factorial : ℝ) *
      ∏ j, (rowWeights (k := k) v₀ θ w j : ℝ))) =
        rowDensity (k := k) K v₀ θ w := by
    rw [prod_rowWeights]
    dsimp [rowDensity]
    field_simp
  rw [heq] at h
  apply h.congr'
  exact Eventually.of_forall (fun H => by simp only [rowCount, Nat.cast_mul]; ring)

/-- Strict inequality of the exact leading coefficients supplies the finite
capacity bound for every sufficiently large real height. -/
theorem eventually_capacity_le (K : ℕ) (v₀ θ : ℚ) (w : Fin m → ℚ)
    (hv₀ : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i)
    (A S η : ℝ) (hA : 0 < A) (hS : 0 < S)
    (hmargin : capacityDensity (k := k) w A S < η * rowDensity (k := k) K v₀ θ w / 2) :
    ∀ᶠ H : ℝ in atTop,
      ((lowModes (k := k) w A S H).card : ℝ) ≤ η * rowCount (k := k) K v₀ θ w H / 2 := by
  have hsmall := (tendsto_lowModes_card w hw A S hA hS).eventually_lt
    (((tendsto_rowCount K v₀ θ w hv₀ hθ hw).const_mul η).div_const 2) hmargin
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with H hH hHpos
  apply le_of_lt
  apply (div_lt_div_iff_of_pos_right (pow_pos hHpos (k + m))).mp
  convert hH using 1
  ring

/-- The transverse weight product cancels exactly. The remaining dimension
factor is the binomial coefficient, not an exponential loss in `m`. -/
theorem density_ratio (K : ℕ) (hK : 0 < K) (v₀ θ : ℚ) (w : Fin m → ℚ)
    (hv₀ : 0 < v₀) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (A S : ℝ) :
    capacityDensity (k := k) w A S / rowDensity (k := k) K v₀ θ w =
      ((k + m).choose k : ℝ) * (v₀ : ℝ) ^ k * A ^ m * S ^ k /
        ((K : ℝ) * (θ : ℝ) ^ m) := by
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hv0 : (v₀ : ℝ) ≠ 0 := by exact_mod_cast hv₀.ne'
  have ht0 : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
  have hprod : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => show (0 : ℝ) < w i by exact_mod_cast hw i)).ne'
  have hkm : ((k + m).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k+m)
  have hk0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hm0 : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hfac : ((k + m).choose k : ℝ) * k.factorial * m.factorial = (k + m).factorial := by
    exact_mod_cast (show (k + m).choose k * k.factorial * m.factorial = (k + m).factorial by
      simpa using Nat.choose_mul_factorial_mul_factorial (show k ≤ k + m by omega))
  dsimp [capacityDensity, rowDensity]
  field_simp
  rw [← hfac]
  ring

/-- The counted product set discharges the coverage hypothesis in the finite
collision argument. The eventual theorem above supplies its capacity bound. -/
theorem collision_degree_sum {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (w : Fin m → ℚ) (hw : ∀ i, 0 < w i) (A S H η : ℝ)
    (hS : 0 ≤ S) (hH : 0 ≤ H)
    (mode : ι → (Fin m → ℕ) × (Fin k → ℕ))
    (coefficient : ((Fin m → ℕ) × (Fin k → ℕ)) → ι → R) (scalar : ι → R)
    (hdet : Matrix.det (fun i j => scalar i * coefficient (mode i) j) ≠ 0)
    (hselected : η * Fintype.card ι ≤
      ((Finset.univ.filter fun i => (∑ j, (w j : ℝ) * (mode i).1 j) ≤ A * H).card : ℝ))
    (hcapacity : ((lowModes (k := k) w A S H).card : ℝ) ≤ η * Fintype.card ι / 2) :
    η * Fintype.card ι * S * H / 2 ≤ ∑ i, ∑ r, ((mode i).2 r : ℝ) := by
  classical
  exact multivariate_collision_degree_sum_lower_bound mode
    (fun γ => (∑ j, (w j : ℝ) * γ j) ≤ A * H) coefficient scalar
    (lowModes w A S H) η S H hS hH hdet
    (fun γ d hγ hd => (mem_lowModes w hw A S H γ d).mpr ⟨hγ, hd⟩)
    hselected hcapacity

end
end GeneralizedLogarithms.MultivariateModeCapacity

/-- info: 'GeneralizedLogarithms.MultivariateModeCapacity.tendsto_lowModes_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateModeCapacity.tendsto_lowModes_card

/-- info: 'GeneralizedLogarithms.MultivariateModeCapacity.tendsto_rowCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateModeCapacity.tendsto_rowCount

/-- info: 'GeneralizedLogarithms.MultivariateModeCapacity.eventually_capacity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateModeCapacity.eventually_capacity_le

/-- info: 'GeneralizedLogarithms.MultivariateModeCapacity.density_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateModeCapacity.density_ratio

/-- info: 'GeneralizedLogarithms.MultivariateModeCapacity.collision_degree_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateModeCapacity.collision_degree_sum
