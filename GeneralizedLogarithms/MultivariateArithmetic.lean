import GeneralizedLogarithms.MultivariateTruncatedMatrix
import LogIrrationalityMeasure.Approximation.MatrixArithmetic

/-!
# Denominator clearing for the actual multilogarithmic matrix

Integer formal series form a subring. Clearing each substituted coordinate
therefore clears every monomial, uniformly over the weighted column simplex.
The longitudinal denominators come from the rational centers; each transverse
coordinate uses one fixed logarithm cutoff, shared among its logarithm terms.
-/

namespace GeneralizedLogarithms.MultivariateArithmetic

noncomputable section
open scoped BigOperators
open MvPowerSeries
open LogIrrationalityMeasure.LogExponent
open MultivariateInterpolationMatrix

section IntegerSeries
variable {σ : Type*}

def integerSeries : Subring (MvPowerSeries σ ℂ) :=
  (MvPowerSeries.map (Int.castRingHom ℂ)).range

theorem C_mem_integerSeries (z : ℂ) (hz : z ∈ (Int.castRingHom ℂ).range) :
    C (σ := σ) z ∈ integerSeries := by
  obtain ⟨q, rfl⟩ := hz
  exact ⟨C q, by simp⟩

theorem C_int_mem_integerSeries (z : ℤ) : C (σ := σ) (z : ℂ) ∈ integerSeries :=
  C_mem_integerSeries _ ⟨z, rfl⟩

theorem X_mem_integerSeries (s : σ) : X s ∈ integerSeries (σ := σ) :=
  ⟨X s, by simp⟩

theorem coeff_integerSeries (f : MvPowerSeries σ ℂ) (hf : f ∈ integerSeries)
    (d : σ →₀ ℕ) : coeff d f ∈ (Int.castRingHom ℂ).range := by
  obtain ⟨g, rfl⟩ := hf
  exact ⟨coeff d g, by simp⟩

theorem map_lift_int (s : σ) (f : PowerSeries ℤ) :
    MvPowerSeries.map (Int.castRingHom ℂ) (f.toMvPowerSeries s) =
      (PowerSeries.map (Int.castRingHom ℂ) f).toMvPowerSeries s := by
  classical
  ext d
  simp only [MvPowerSeries.coeff_map, PowerSeries.toMvPowerSeries_eq_subst,
    PowerSeries.coeff_subst_single, PowerSeries.coeff_map]
  split_ifs <;> simp

theorem cleared_log_lift_integer (s : σ) (T : ℕ) :
    C (Nat.lcmUpto T : ℂ) *
      (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ).toMvPowerSeries s ∈
        integerSeries := by
  obtain ⟨P, hP⟩ := Arithmetic.exists_cleared_log_trunc T
  refine ⟨(P : PowerSeries ℤ).toMvPowerSeries s, ?_⟩
  rw [map_lift_int, ← Polynomial.polynomial_map_coe, hP]
  simp only [Polynomial.coe_mul, Polynomial.coe_C, map_mul, PowerSeries.toMvPowerSeries_C]

variable [Fintype σ]

omit [Fintype σ] in
theorem cleared_power_integer (D e n : ℕ) (f : MvPowerSeries σ ℂ) (hn : n ≤ e)
    (hf : C (D : ℂ) * f ∈ integerSeries) :
    C ((D : ℂ) ^ e) * f ^ n ∈ integerSeries := by
  have hD := C_int_mem_integerSeries (σ := σ) (D : ℤ)
  have h := integerSeries.mul_mem (integerSeries.pow_mem hD (e - n))
    (integerSeries.pow_mem hf n)
  have he : e = (e - n) + n := (Nat.sub_add_cancel hn).symm
  rw [he, map_pow, pow_add]
  simpa only [Int.cast_natCast, mul_pow, mul_assoc] using h

theorem cleared_monomial_coeff_integer
    (F : MvPolynomial σ ℂ →ₐ[ℂ] MvPowerSeries σ ℂ)
    (D e : σ → ℕ) (d q : σ →₀ ℕ) (hd : ∀ s, d s ≤ e s)
    (hF : ∀ s, C (D s : ℂ) * F (MvPolynomial.X s) ∈ integerSeries) :
    (∏ s, (D s : ℂ) ^ e s) * coeff q (F (MvPolynomial.monomial d 1)) ∈
      (Int.castRingHom ℂ).range := by
  classical
  have hprod := (integerSeries (σ := σ)).prod_mem (t := Finset.univ)
    (fun s _ => cleared_power_integer (D s) (e s) (d s) (F (MvPolynomial.X s)) (hd s) (hF s))
  have hmon : F (MvPolynomial.monomial d 1) = ∏ s, F (MvPolynomial.X s) ^ d s := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
    simp only [map_pow]
  have he : (∏ s, C ((D s : ℂ) ^ e s) * F (MvPolynomial.X s) ^ d s) =
      C (∏ s, (D s : ℂ) ^ e s) * F (MvPolynomial.monomial d 1) := by
    rw [Finset.prod_mul_distrib, ← map_prod, hmon]
  rw [he] at hprod
  simpa only [coeff_C_mul] using coeff_integerSeries _ hprod q

end IntegerSeries

variable {k m K : ℕ}

def center (α : Fin k → ℚ) (p : Fin m → ℤ) (j : ℕ) : Fin k ⊕ Fin m → ℂ :=
  fun s => (MultivariateRationalJet.approximationCenter α p j s : ℂ)

def jet (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (T : Fin m → ℕ) (j : ℕ) :=
  MultivariateLogPolynomialAdapter.truncatedFormalJet a (center α p j) (fun i _ => T i)

def coordinateDenominator (α : Fin k → ℚ) (T : Fin m → ℕ) (J : ℕ) :
    Fin k ⊕ Fin m → ℕ :=
  Sum.elim (fun r => (α r).den ^ J) (fun i => Nat.lcmUpto (T i))

theorem coordinateDenominator_pos (α : Fin k → ℚ) (T : Fin m → ℕ) (J : ℕ)
    (s : Fin k ⊕ Fin m) : 0 < coordinateDenominator α T J s := by
  cases s with
  | inl r => exact pow_pos (α r).pos J
  | inr i => exact Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i))

theorem cleared_coordinate_integer (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ)
    (p : Fin m → ℤ) (T : Fin m → ℕ) (j J : ℕ) (hj : j ≤ J) (s : Fin k ⊕ Fin m) :
    C (coordinateDenominator α T J s : ℂ) * jet α a p T j (MvPolynomial.X s) ∈
      integerSeries := by
  classical
  cases s with
  | inl r =>
    have hz : ((α r).den : ℂ) ^ J * (α r : ℂ) ^ j ∈ (Int.castRingHom ℂ).range := by
      simpa using InterpolationMatrix.den_pow_mul_rat_pow_mem (α r) 1 j J hj
    have hh := integerSeries.mul_mem (C_mem_integerSeries (σ := Fin k ⊕ Fin m) _ hz)
      (integerSeries.add_mem integerSeries.one_mem (X_mem_integerSeries (Sum.inl r)))
    simpa only [jet, MultivariateFormalLogShift.truncatedFormalJet_Y, center,
      MultivariateRationalJet.approximationCenter_Y, coordinateDenominator, Sum.elim_inl,
      Nat.cast_pow, Rat.cast_pow, map_mul, mul_assoc] using hh
  | inr i =>
    have hC : C (σ := Fin k ⊕ Fin m) ((Nat.lcmUpto (T i) : ℂ) *
        (-(j : ℂ) * (p i : ℂ))) ∈ integerSeries := by
      convert C_int_mem_integerSeries (σ := Fin k ⊕ Fin m)
        ((Nat.lcmUpto (T i) : ℤ) * (-(j : ℤ) * p i)) using 1 <;> push_cast <;> rfl
    have hX := integerSeries.mul_mem
      (C_int_mem_integerSeries (σ := Fin k ⊕ Fin m) (Nat.lcmUpto (T i)))
      (X_mem_integerSeries (Sum.inr i))
    have hlog : ∑ r : Fin k, C (a i r : ℂ) *
        (C (Nat.lcmUpto (T i) : ℂ) *
          (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ).toMvPowerSeries
            (Sum.inl r)) ∈ integerSeries (σ := Fin k ⊕ Fin m) := by
      exact integerSeries.sum_mem fun r _ => integerSeries.mul_mem
        (C_int_mem_integerSeries (a i r)) (cleared_log_lift_integer _ _)
    have hh := integerSeries.add_mem (integerSeries.add_mem hC hX) hlog
    simp only [jet, MultivariateFormalLogShift.truncatedFormalJet_X, center,
      MultivariateRationalJet.approximationCenter_X, coordinateDenominator, Sum.elim_inr,
      Rat.cast_mul, Rat.cast_neg, Rat.cast_natCast, Rat.cast_intCast,
      mul_add, Finset.mul_sum, ← map_mul] at hh ⊢
    convert hh using 1
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    ring

def denominator (α : Fin k → ℚ) (T : Fin m → ℕ) (J : ℕ)
    (w : Fin k ⊕ Fin m → ℝ) (H : ℝ) : ℝ :=
  ∏ s, (coordinateDenominator α T J s : ℝ) ^ ⌊H / w s⌋₊

theorem denominator_pos (α : Fin k → ℚ) (T : Fin m → ℕ) (J : ℕ)
    (w : Fin k ⊕ Fin m → ℝ) (H : ℝ) : 0 < denominator α T J w H := by
  exact Finset.prod_pos (fun s _ => pow_pos (by exact_mod_cast coordinateDenominator_pos α T J s) _)

theorem column_coordinate_le (w : Fin k ⊕ Fin m → ℝ) (hw : ∀ s, 0 < w s)
    (H : ℝ) (e : Column w H) (s : Fin k ⊕ Fin m) : e.val s ≤ ⌊H / w s⌋₊ := by
  have he := (mem_columnExponents w hw H e.val).mp e.property
  apply Nat.le_floor
  apply (le_div_iff₀ (hw s)).mpr
  apply le_trans _ he
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul]
  exact Finset.single_le_sum (f := fun i => (e.val i : ℝ) * w i)
    (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hw i).le) (Finset.mem_univ s)

def actualMatrix (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ) (p : Fin m → ℤ)
    (T : Fin m → ℕ) (K : ℕ) (w : Fin k ⊕ Fin m → ℝ)
    (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) : Matrix (Row (Fin K) v H) (Column w H) ℂ :=
  MultivariateTruncatedMatrix.packetMatrix (fun j : Fin K => jet α a p T j.val) w v H

theorem matrix_entries_cleared (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ)
    (p : Fin m → ℤ) (T : Fin m → ℕ) (K : ℕ)
    (w : Fin k ⊕ Fin m → ℝ) (hw : ∀ s, 0 < w s)
    (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) (ρ : Row (Fin K) v H) (e : Column w H) :
    (denominator α T (K - 1) w H : ℂ) * actualMatrix α a p T K w v H ρ e ∈
      (Int.castRingHom ℂ).range := by
  have hh := cleared_monomial_coeff_integer (jet α a p T ρ.1.val)
    (coordinateDenominator α T (K - 1)) (fun s => ⌊(H : ℝ) / w s⌋₊) e.val ρ.2.val
    (column_coordinate_le w hw H e)
    (cleared_coordinate_integer α a p T ρ.1.val (K - 1) (by have := ρ.1.isLt; omega))
  simpa only [denominator, Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_natCast,
    actualMatrix, MultivariateTruncatedMatrix.packetMatrix] using hh

/-- A logarithmic arithmetic lower bound for every nonzero selected minor of
the actual matrix. The clearing property is proved above, not an input. -/
theorem determinant_lower_bound (α : Fin k → ℚ) (a : Fin m → Fin k → ℤ)
    (p : Fin m → ℤ) (T : Fin m → ℕ) (K : ℕ)
    (w : Fin k ⊕ Fin m → ℝ) (hw : ∀ s, 0 < w s)
    (v : Fin k ⊕ Fin m → ℚ) (H : ℚ)
    (selection : Row (Fin K) v H → Column w H)
    (hne : ((actualMatrix α a p T K w v H).submatrix id selection).det ≠ 0) :
    -(Fintype.card (Row (Fin K) v H) : ℝ) * Real.log (denominator α T (K - 1) w H) ≤
      Real.log ‖((actualMatrix α a p T K w v H).submatrix id selection).det‖ := by
  classical
  have h := Arithmetic.cleared_det_log_bound_with_denominator
    ((actualMatrix α a p T K w v H).submatrix id selection) (fun _ => 1) (fun _ => 1)
    (denominator α T (K - 1) w H) (denominator_pos α T (K - 1) w H)
    (fun _ => zero_lt_one) (fun _ => zero_lt_one) hne (fun ρ b => by
      simpa only [Complex.ofReal_one, one_mul, mul_one, Matrix.submatrix_apply, id_eq] using
        matrix_entries_cleared α a p T K w hw v H ρ (selection b))
  simpa using h

end
end GeneralizedLogarithms.MultivariateArithmetic

/-- info: 'GeneralizedLogarithms.MultivariateArithmetic.matrix_entries_cleared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateArithmetic.matrix_entries_cleared

/-- info: 'GeneralizedLogarithms.MultivariateArithmetic.determinant_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateArithmetic.determinant_lower_bound
