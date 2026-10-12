import LogIrrationalityMeasure.Approximation.Exponent

/-!
# Foundations for logarithmic linear forms

The higher-rank lower bound is defined here and proved in `Main.lean`.
Nonvanishing is proved from an explicitly named rank-one lower-bound input,
discharged using the pinned logarithm formalization in `OriginalRankOne.lean`.
-/

namespace GeneralizedLogarithms

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent

/-- Integer multiplicative relations among a finite family are trivial. -/
def MultiplicativelyIndependent {k : ℕ} (α : Fin k → ℚ) : Prop :=
  ∀ a : Fin k → ℤ, (∏ i, α i ^ a i) = 1 → a = 0

/-- The real logarithmic linear form, including its integer constant term. -/
noncomputable def linearForm {k : ℕ} (α : Fin k → ℚ)
    (p : ℤ) (a : Fin k → ℤ) : ℝ :=
  (p : ℝ) + ∑ i, (a i : ℝ) * Real.log (α i)

/-- The exact height used in the proposed theorem. -/
def coefficientHeight {k : ℕ} (p : ℤ) (a : Fin k → ℤ) : ℕ :=
  max 2 (max p.natAbs (Finset.univ.sup fun i => (a i).natAbs))

/-- The higher-rank conclusion proved in `Main.lean`. -/
def EventualLinearFormLowerBound {k : ℕ} (α : Fin k → ℚ) : Prop :=
  ∀ ν : ℝ, (k : ℝ) < ν → ∃ H₀ : ℕ, ∀ (p : ℤ) (a : Fin k → ℤ),
    H₀ ≤ coefficientHeight p a →
      (coefficientHeight p a : ℝ) ^ (-ν) ≤ |linearForm α p a|

/-- The old, rank-one result is an explicit input to the nonvanishing reduction. -/
def RankOneLogarithmBounds : Prop :=
  ∀ β : ℚ, 0 < β → β ≠ 1 → LogEventualLowerBound β

theorem two_le_coefficientHeight {k : ℕ} (p : ℤ) (a : Fin k → ℤ) :
    2 ≤ coefficientHeight p a := le_max_left _ _

theorem natAbs_constant_le_height {k : ℕ} (p : ℤ) (a : Fin k → ℤ) :
    p.natAbs ≤ coefficientHeight p a :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem natAbs_coefficient_le_height {k : ℕ} (p : ℤ) (a : Fin k → ℤ) (i : Fin k) :
    (a i).natAbs ≤ coefficientHeight p a := by
  exact (Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)).trans
    ((le_max_right _ _).trans (le_max_right _ _))

@[simp] theorem coefficientHeight_zero (k : ℕ) :
    coefficientHeight 0 (0 : Fin k → ℤ) = 2 := by
  simp [coefficientHeight]

theorem rational_monomial_pos {k : ℕ} (α : Fin k → ℚ)
    (hα : ∀ i, 0 < α i) (a : Fin k → ℤ) :
    0 < ∏ i, α i ^ a i :=
  Finset.prod_pos (fun i _ => zpow_pos (hα i) _)

theorem log_rational_monomial {k : ℕ} (α : Fin k → ℚ)
    (hα : ∀ i, 0 < α i) (a : Fin k → ℤ) :
    Real.log ((∏ i, α i ^ a i : ℚ) : ℝ) =
      ∑ i, (a i : ℝ) * Real.log (α i) := by
  push_cast
  rw [Real.log_prod]
  · simp only [Real.log_zpow]
  · intro i _
    exact zpow_ne_zero _ (by exact_mod_cast (hα i).ne')

/-- A nonzero exponent vector yields an irrational logarithmic sum. -/
theorem irrational_log_sum (hbase : RankOneLogarithmBounds)
    {k : ℕ} (α : Fin k → ℚ) (hα : ∀ i, 0 < α i)
    (hind : MultiplicativelyIndependent α) (a : Fin k → ℤ) (ha : a ≠ 0) :
    Irrational (∑ i, (a i : ℝ) * Real.log (α i)) := by
  have hβ : (∏ i, α i ^ a i) ≠ 1 := fun h => ha (hind a h)
  have hi := irrational_of_eventualLowerBound
    (hbase _ (rational_monomial_pos α hα a) hβ)
  rwa [log_rational_monomial α hα a] at hi

/-- Nonvanishing for every nonzero integer coefficient tuple. -/
theorem linearForm_ne_zero (hbase : RankOneLogarithmBounds)
    {k : ℕ} (α : Fin k → ℚ) (hα : ∀ i, 0 < α i)
    (hind : MultiplicativelyIndependent α) (p : ℤ) (a : Fin k → ℤ)
    (hne : p ≠ 0 ∨ a ≠ 0) : linearForm α p a ≠ 0 := by
  by_cases ha : a = 0
  · have hp : p ≠ 0 := hne.resolve_right (not_not_intro ha)
    simpa [linearForm, ha] using (Int.cast_ne_zero.mpr hp : (p : ℝ) ≠ 0)
  · intro hzero
    have hi := irrational_log_sum hbase α hα hind a ha
    apply hi.ne_rat (-p)
    push_cast
    dsimp [linearForm] at hzero
    linarith

/-- Heights exceeding two exclude the one exceptional zero tuple. -/
theorem linearForm_ne_zero_of_height (hbase : RankOneLogarithmBounds)
    {k : ℕ} (α : Fin k → ℚ) (hα : ∀ i, 0 < α i)
    (hind : MultiplicativelyIndependent α) (p : ℤ) (a : Fin k → ℤ)
    (hheight : 2 < coefficientHeight p a) : linearForm α p a ≠ 0 := by
  apply linearForm_ne_zero hbase α hα hind p a
  by_contra h
  push Not at h
  rcases h with ⟨rfl, rfl⟩
  simp at hheight

/-- There are only finitely many coefficient tuples of bounded height. -/
theorem finite_bounded_height (k N : ℕ) :
    {x : ℤ × (Fin k → ℤ) | coefficientHeight x.1 x.2 ≤ N}.Finite := by
  have hint : (Set.Icc (-(N : ℤ)) (N : ℤ)).Finite := Set.finite_Icc _ _
  have hvec : {a : Fin k → ℤ | ∀ i, a i ∈ Set.Icc (-(N : ℤ)) (N : ℤ)}.Finite :=
    Set.Finite.pi' (fun _ => hint)
  apply (hint.prod hvec).subset
  rintro ⟨p, a⟩ hx
  have hp := (natAbs_constant_le_height p a).trans hx
  have ha := fun i => (natAbs_coefficient_le_height p a i).trans hx
  constructor
  · constructor <;> omega
  · intro i
    have hai := ha i
    change -(N : ℤ) ≤ a i ∧ a i ≤ N
    constructor <;> omega

/-- The zero-dimensional induction case: a nonzero integer cannot be an
exceptional small linear form when all logarithmic coefficients vanish. -/
theorem lower_bound_zero_coefficients {k : ℕ} (α : Fin k → ℚ)
    (p : ℤ) (hp : p ≠ 0) (ν : ℝ) (hν : 0 ≤ ν) :
    (coefficientHeight p (0 : Fin k → ℤ) : ℝ) ^ (-ν) ≤
      |linearForm α p 0| := by
  have hheight : (1 : ℝ) ≤ coefficientHeight p (0 : Fin k → ℤ) := by
    exact_mod_cast (show 1 ≤ coefficientHeight p (0 : Fin k → ℤ) from
      le_trans (by omega) (two_le_coefficientHeight p 0))
  have hpabs : (1 : ℝ) ≤ |(p : ℝ)| := by
    have habs : (1 : ℤ) ≤ |p| := by
      have hpos : (0 : ℤ) < |p| := abs_pos.mpr hp
      omega
    exact_mod_cast habs
  simpa [linearForm] using
    (Real.rpow_le_one_of_one_le_of_nonpos hheight (neg_nonpos.mpr hν)).trans hpabs

/-- info: 'GeneralizedLogarithms.linearForm_ne_zero_of_height' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms linearForm_ne_zero_of_height

/-- info: 'GeneralizedLogarithms.finite_bounded_height' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finite_bounded_height

/-- info: 'GeneralizedLogarithms.lower_bound_zero_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lower_bound_zero_coefficients

end GeneralizedLogarithms
