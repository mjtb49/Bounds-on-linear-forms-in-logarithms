import GeneralizedLogarithms.MultivariateArithmetic

/-!
# Normalized arithmetic estimates for multilogarithmic interpolation

The logarithmic denominator cost is linear in the height. The normalized
determinant bound is uniform in the integer approximation coefficients. The
last theorem connects the geometric nonzero-minor construction to this bound.
-/

namespace GeneralizedLogarithms.MultivariateArithmeticBounds

noncomputable section
open scoped BigOperators
open Filter
open LogIrrationalityMeasure.LogExponent
open MultivariateInterpolationMatrix MultivariateArithmetic

variable {k m K : ℕ}

def cost (α : Fin k → ℚ) (T : Fin m → ℕ) (J : ℕ) (w : Fin k ⊕ Fin m → ℝ) : ℝ :=
  ∑ s, Real.log (coordinateDenominator α T J s) / w s

theorem log_denominator_le (α : Fin k → ℚ) (T : Fin m → ℕ) (J : ℕ)
    (w : Fin k ⊕ Fin m → ℝ) (hw : ∀ s, 0 < w s) (H : ℝ) (hH : 0 ≤ H) :
    Real.log (denominator α T J w H) ≤ H * cost α T J w := by
  rw [denominator, Real.log_prod (fun s _ =>
    (pow_pos (show (0 : ℝ) < coordinateDenominator α T J s by
      exact_mod_cast coordinateDenominator_pos α T J s) _).ne')]
  simp_rw [Real.log_pow]
  rw [cost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hlog : 0 ≤ Real.log (coordinateDenominator α T J s : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast coordinateDenominator_pos α T J s
  have hf := Nat.floor_le (div_nonneg hH (hw s).le)
  have hh := mul_le_mul_of_nonneg_right hf hlog
  convert hh using 1 <;> ring

theorem cost_le (α : Fin k → ℚ) (T : Fin m → ℕ) (J : ℕ)
    (w : Fin k ⊕ Fin m → ℝ) (hw : ∀ s, 0 < w s) :
    cost α T J w ≤
      (J : ℝ) * (∑ r, Real.log (α r).den / w (Sum.inl r)) +
        Arithmetic.lcmConstant * ∑ i, (T i : ℝ) / w (Sum.inr i) := by
  rw [cost, Fintype.sum_sum_type]
  simp only [coordinateDenominator, Sum.elim_inl, Sum.elim_inr, Nat.cast_pow, Real.log_pow]
  have hY : (∑ r, (J : ℝ) * Real.log (α r).den / w (Sum.inl r)) =
      (J : ℝ) * ∑ r, Real.log (α r).den / w (Sum.inl r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [hY]
  apply add_le_add_right
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hh := div_le_div_of_nonneg_right (Arithmetic.log_lcmUpto_le (T i)) (hw (Sum.inr i)).le
  convert hh using 1 <;> ring

theorem cutoff_cost_le (α : Fin k → ℚ) (J : ℕ) (w : Fin k ⊕ Fin m → ℝ)
    (hw : ∀ s, 0 < w s) (F v₀ : ℝ) (hF : 0 ≤ F) (hv₀ : 0 < v₀) :
    cost α (fun i => ⌈F * w (Sum.inr i) / v₀⌉₊) J w ≤
      (J : ℝ) * (∑ r, Real.log (α r).den / w (Sum.inl r)) +
        Arithmetic.lcmConstant * F * m / v₀ +
          Arithmetic.lcmConstant * ∑ i, 1 / w (Sum.inr i) := by
  have hh := cost_le α (fun i => ⌈F * w (Sum.inr i) / v₀⌉₊) J w hw
  have hsum := Arithmetic.sum_ceil_truncation_div_le Finset.univ
    (fun i => w (Sum.inr i)) F v₀ hF hv₀ (fun i _ => hw (Sum.inr i))
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum Arithmetic.lcmConstant_pos.le
  calc
    _ ≤ (J : ℝ) * (∑ r, Real.log (α r).den / w (Sum.inl r)) +
        Arithmetic.lcmConstant * (F * m / v₀ + ∑ i, 1 / w (Sum.inr i)) :=
      hh.trans (add_le_add_right hmul _)
    _ = _ := by ring

theorem row_card_pos (K : ℕ) (hK : 0 < K) (v : Fin k ⊕ Fin m → ℚ)
    (hv : ∀ s, 0 < v s) (H : ℚ) (hH : 0 < H) : 0 < Fintype.card (Row (Fin K) v H) := by
  classical
  let z : ↥(jetExponents v H) := ⟨0, (mem_jetExponents v hv H 0).mpr (by simpa using hH)⟩
  let : Nonempty (Row (Fin K) v H) := ⟨(⟨0, hK⟩, z)⟩
  exact Fintype.card_pos

theorem normalized_determinant_lower_bound (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ)
    (p : Fin m → ℤ) (T : Fin m → ℕ) (K : ℕ) (hK : 0 < K)
    (w : Fin k ⊕ Fin m → ℝ) (hw : ∀ s, 0 < w s)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ s, 0 < v s) (H : ℚ) (hH : 0 < H)
    (selection : Row (Fin K) v H → Column w H)
    (hne : ((actualMatrix α a p T K w v H).submatrix id selection).det ≠ 0) :
    -cost α T (K - 1) w ≤
      Real.log ‖((actualMatrix α a p T K w v H).submatrix id selection).det‖ /
        ((Fintype.card (Row (Fin K) v H) : ℝ) * H) := by
  have hM : (0 : ℝ) < Fintype.card (Row (Fin K) v H) := by
    exact_mod_cast row_card_pos K hK v hv H hH
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  apply (le_div_iff₀ (mul_pos hM hH')).mpr
  have hlower := determinant_lower_bound α a p T K w hw v H selection hne
  have hcost := log_denominator_le α T (K - 1) w hw H hH'.le
  nlinarith [mul_le_mul_of_nonneg_left hcost hM.le]

variable [LinearOrder (Fin k ⊕ Fin m)]

/-- Geometry and arithmetic now apply to the same actual determinant. All
entry integrality and denominator estimates are discharged. -/
theorem eventual_minor_with_arithmetic_bound (hk : 0 < k)
    (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ) (K : ℕ) (hK : 0 < K)
    (d : MultivariateCurveMargin.NumericalData a (fun j : Fin K => center α p j.val))
    (T : Fin m → ℕ) (hT : ∀ i r, d.v (Sum.inr i) ≤ (T i : ℚ) * d.v (Sum.inl r)) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
      ∃ selection : Row (Fin K) d.v (n * R) →
          Column (fun s => (d.w s : ℝ)) (((n : ℚ) * (R : ℚ) : ℚ) : ℝ),
        let A := (actualMatrix α a p T K (fun s => (d.w s : ℝ)) d.v (n * R)).submatrix id selection
        A.det ≠ 0 ∧ -cost α T (K - 1) (fun s => (d.w s : ℝ)) ≤
          Real.log ‖A.det‖ / ((Fintype.card (Row (Fin K) d.v (n * R)) : ℝ) * ((n : ℚ) * R : ℚ)) := by
  obtain ⟨R, hR, h⟩ := MultivariateTruncatedMatrix.eventual_rational_minor hk a
    (fun j : Fin K => MultivariateRationalJet.approximationCenter α p j.val) d (fun i _ => T i) hT
  refine ⟨R, hR, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  obtain ⟨s, hs, hdet⟩ := hn
  refine ⟨s, ?_⟩
  dsimp only
  have hcast := MultivariateTruncatedMatrix.matrix_cast a
    (fun j : Fin K => MultivariateRationalJet.approximationCenter α p j.val) (fun i _ => T i)
    (fun t => (d.w t : ℝ)) d.v (n * R)
  have hne : ((actualMatrix α a p T K (fun t => (d.w t : ℝ)) d.v (n * R)).submatrix id s).det ≠ 0 := by
    change ((MultivariateTruncatedMatrix.packetMatrix
      (fun j : Fin K => MultivariateLogPolynomialAdapter.truncatedFormalJet a
        (fun t => (MultivariateRationalJet.approximationCenter α p j.val t : ℂ))
        (fun i _ => T i)) (fun t => (d.w t : ℝ)) d.v (n * R)).submatrix id s).det ≠ 0
    rw [← hcast]
    change (((MultivariateTruncatedMatrix.matrix a
      (fun j : Fin K => MultivariateRationalJet.approximationCenter α p j.val) (fun i _ => T i)
      (fun t => (d.w t : ℝ)) d.v (n * R)).submatrix id s).map (algebraMap ℚ ℂ)).det ≠ 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero (algebraMap ℚ ℂ)).mpr hdet
  refine ⟨hne, normalized_determinant_lower_bound α a p T K hK
    (fun t => (d.w t : ℝ)) (fun t => by exact_mod_cast d.w_pos t) d.v d.v_pos
    (n * R) ?_ s hne⟩
  exact mul_pos (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hR)

end
end GeneralizedLogarithms.MultivariateArithmeticBounds

/-- info: 'GeneralizedLogarithms.MultivariateArithmeticBounds.normalized_determinant_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateArithmeticBounds.normalized_determinant_lower_bound

/-- info: 'GeneralizedLogarithms.MultivariateArithmeticBounds.eventual_minor_with_arithmetic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateArithmeticBounds.eventual_minor_with_arithmetic_bound
