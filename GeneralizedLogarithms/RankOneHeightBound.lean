import GeneralizedLogarithms.OriginalRankOne

/-!
# The rank-one base case with the exact coefficient height

The original rational-approximation exponent two gives linear-form exponent
one. Large denominators use that theorem directly; bounded denominators and
large coefficient height force the constant coefficient, and hence the form,
to be large. Both signs and the zero logarithmic coefficient are included.
-/

namespace GeneralizedLogarithms.RankOneHeightBound

open LogIrrationalityMeasure LogExponent

theorem signed_coefficient_bound (x ν : ℝ) (Q : ℕ) (hQ : 2 ≤ Q)
    (hbound : ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-(ν + 1)) ≤ |x - (p : ℝ) / q|)
    (p a : ℤ) (ha : Q ≤ a.natAbs) :
    (a.natAbs : ℝ) ^ (-ν) ≤ |(p : ℝ) + a * x| := by
  have hapos : 0 < (a.natAbs : ℝ) := by exact_mod_cast (show 0 < a.natAbs by omega)
  have hpower : (a.natAbs : ℝ) ^ (-ν) =
      (a.natAbs : ℝ) * (a.natAbs : ℝ) ^ (-(ν + 1)) := by
    calc
      _ = (a.natAbs : ℝ) ^ (1 + -(ν + 1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hapos, Real.rpow_one]
  rw [hpower]
  by_cases hsign : 0 ≤ a
  · have hcast : (a.natAbs : ℝ) = (a : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonneg hsign]
    have ha0 : (a : ℝ) ≠ 0 := by rw [← hcast]; exact hapos.ne'
    have heq : (a.natAbs : ℝ) * |x - ((-p : ℤ) : ℝ) / a.natAbs| =
        |(p : ℝ) + a * x| := by
      calc
        _ = |(a.natAbs : ℝ) * (x - ((-p : ℤ) : ℝ) / a.natAbs)| := by
          rw [abs_mul, abs_of_pos hapos]
        _ = _ := by
          congr 1
          rw [hcast, Int.cast_neg]
          field_simp
          ring
    exact (mul_le_mul_of_nonneg_left (hbound (-p) a.natAbs ha) hapos.le).trans_eq heq
  · have hcast : (a.natAbs : ℝ) = -(a : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonpos (lt_of_not_ge hsign).le, Int.cast_neg]
    have ha0 : (a : ℝ) ≠ 0 := by intro hz; rw [hcast, hz, neg_zero] at hapos; linarith
    have heq : (a.natAbs : ℝ) * |x - (p : ℝ) / a.natAbs| =
        |(p : ℝ) + a * x| := by
      have hinner : (a.natAbs : ℝ) * (x - (p : ℝ) / a.natAbs) =
          -((p : ℝ) + a * x) := by rw [hcast]; field_simp; ring
      calc
        _ = |(a.natAbs : ℝ) * (x - (p : ℝ) / a.natAbs)| := by
          rw [abs_mul, abs_of_pos hapos]
        _ = _ := by rw [hinner, abs_neg]
    exact (mul_le_mul_of_nonneg_left (hbound p a.natAbs ha) hapos.le).trans_eq heq

/-- The exact max-height version for an arbitrary real number satisfying the
original eventual rational-approximation bound. -/
theorem eventual_max_height_bound (x : ℝ) (hx : EventualLowerBound x)
    (ν : ℝ) (hν : 1 < ν) :
    ∃ H₀ : ℕ, ∀ p a : ℤ, H₀ ≤ max 2 (max p.natAbs a.natAbs) →
      ((max 2 (max p.natAbs a.natAbs) : ℕ) : ℝ) ^ (-ν) ≤ |(p : ℝ) + a * x| := by
  obtain ⟨Q, hQ, hbound⟩ := hx (ν + 1) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((Q : ℝ) + 3) ((Q : ℝ) * |x| + 3))
  have hNQ : (Q : ℝ) + 3 < N := (le_max_left _ _).trans_lt hN
  have hNx : (Q : ℝ) * |x| + 3 < N := (le_max_right _ _).trans_lt hN
  have hNQnat : Q + 3 < N := by exact_mod_cast hNQ
  refine ⟨N, fun p a hH => ?_⟩
  let H := max 2 (max p.natAbs a.natAbs)
  change (H : ℝ) ^ (-ν) ≤ _
  by_cases ha : Q ≤ a.natAbs
  · have haH : (a.natAbs : ℝ) ≤ H := by
      exact_mod_cast ((le_max_right p.natAbs a.natAbs).trans (le_max_right 2 _))
    have hapos : 0 < (a.natAbs : ℝ) := by exact_mod_cast (show 0 < a.natAbs by omega)
    exact (Real.rpow_le_rpow_of_nonpos hapos haH (by linarith)).trans
      (signed_coefficient_bound x ν Q hQ hbound p a ha)
  · have hpN : N ≤ p.natAbs := by omega
    have hpNreal : (N : ℝ) ≤ |(p : ℝ)| := by
      have hh : (N : ℝ) ≤ (p.natAbs : ℝ) := by exact_mod_cast hpN
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    have haQ : |(a : ℝ)| ≤ Q := by
      have hh : (a.natAbs : ℝ) ≤ Q := by exact_mod_cast (show a.natAbs ≤ Q by omega)
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
    have hpabs : |(p : ℝ)| ≤ |(p : ℝ) + a * x| + |(a : ℝ) * x| := by
      simpa only [add_neg_cancel_right, abs_neg] using
        (abs_add_le ((p : ℝ) + a * x) (-((a : ℝ) * x)))
    have hamul : |(a : ℝ) * x| ≤ Q * |x| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right haQ (abs_nonneg x)
    have hone : (1 : ℝ) ≤ |(p : ℝ) + a * x| := by linarith
    apply (Real.rpow_le_one_of_one_le_of_nonpos (x := (H : ℝ)) ?_ (by linarith)).trans hone
    exact_mod_cast (show 1 ≤ H by dsimp [H]; omega)

/-- The full rank-one target, with the same height and exponent convention as
the proposed higher-rank predicate. -/
theorem eventualLowerBound_rank_one (α : Fin 1 → ℚ)
    (hα : ∀ i, 0 < α i) (hind : MultiplicativelyIndependent α) :
    EventualLinearFormLowerBound α := by
  have hne : α 0 ≠ 1 := by
    intro h
    have hz := hind (fun _ => 1) (by simp [h])
    have hh := congrFun hz 0
    norm_num at hh
  intro ν hν
  obtain ⟨N, hN⟩ := eventual_max_height_bound (Real.log (α 0))
    (original_rankOneLogarithmBounds (α 0) (hα 0) hne) ν (by simpa using hν)
  refine ⟨N, fun p a hH => ?_⟩
  have hh : coefficientHeight p a = max 2 (max p.natAbs (a 0).natAbs) := by
    simp [coefficientHeight]
  rw [hh] at hH ⊢
  simpa [linearForm] using hN p (a 0) hH

end GeneralizedLogarithms.RankOneHeightBound

/-- info: 'GeneralizedLogarithms.RankOneHeightBound.eventual_max_height_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.RankOneHeightBound.eventual_max_height_bound

/-- info: 'GeneralizedLogarithms.RankOneHeightBound.eventualLowerBound_rank_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.RankOneHeightBound.eventualLowerBound_rank_one
