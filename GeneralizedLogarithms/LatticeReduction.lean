import GeneralizedLogarithms.Foundations
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Integer changes of logarithmic coordinates

An independent integer family gives a new multiplicatively independent family
of positive rational monomials. The logarithmic form is unchanged after applying
the corresponding coefficient map. These are algebraic ingredients for a
dimension reduction; no eventual lower bound is assumed or concluded here.
-/

namespace GeneralizedLogarithms

open scoped BigOperators

/-- The original coefficients obtained from coefficients in an integer row family. -/
def integerCombination {r k : ℕ} (v : Fin r → Fin k → ℤ)
    (b : Fin r → ℤ) : Fin k → ℤ :=
  fun j => ∑ s, b s * v s j

/-- The positive rational generators associated to an integer row family. -/
def monomialBasis {r k : ℕ} (α : Fin k → ℚ) (v : Fin r → Fin k → ℤ) :
    Fin r → ℚ :=
  fun s => ∏ j, α j ^ v s j

@[simp] theorem integerCombination_zero {r k : ℕ} (v : Fin r → Fin k → ℤ) :
    integerCombination v 0 = 0 := by
  ext j
  simp [integerCombination]

theorem integerCombination_eq_sum_smul {r k : ℕ} (v : Fin r → Fin k → ℤ)
    (b : Fin r → ℤ) : integerCombination v b = ∑ s, b s • v s := by
  ext j
  simp [integerCombination, Finset.sum_apply]

/-- Integer linear independence supplies the injectivity needed for relations. -/
theorem integerCombination_injective {r k : ℕ} (v : Fin r → Fin k → ℤ)
    (hv : LinearIndependent ℤ v) : Function.Injective (integerCombination v) := by
  intro b c hbc
  apply hv.fintypeLinearCombination_injective
  simpa only [integerCombination_eq_sum_smul, Fintype.linearCombination_apply] using hbc

/-- Membership in the integer span is precisely representability in these coordinates. -/
theorem mem_integer_span_iff {r k : ℕ} (v : Fin r → Fin k → ℤ) (a : Fin k → ℤ) :
    a ∈ Submodule.span ℤ (Set.range v) ↔ ∃ b, integerCombination v b = a := by
  simp only [integerCombination_eq_sum_smul, Submodule.mem_span_range_iff_exists_fun]

/-- Coefficients in an independent integer spanning family are unique. -/
theorem existsUnique_integerCombination {r k : ℕ} (v : Fin r → Fin k → ℤ)
    (hv : LinearIndependent ℤ v) (a : Fin k → ℤ)
    (ha : a ∈ Submodule.span ℤ (Set.range v)) :
    ∃! b, integerCombination v b = a := by
  obtain ⟨b, hb⟩ := (mem_integer_span_iff v a).mp ha
  refine ⟨b, hb, ?_⟩
  intro c hc
  exact integerCombination_injective v hv (hc.trans hb.symm)

theorem monomialBasis_pos {r k : ℕ} (α : Fin k → ℚ)
    (hα : ∀ j, 0 < α j) (v : Fin r → Fin k → ℤ) (s : Fin r) :
    0 < monomialBasis α v s :=
  rational_monomial_pos α hα (v s)

private theorem rational_zpow_sum {ι : Type*} (s : Finset ι) (x : ℚ)
    (hx : x ≠ 0) (b : ι → ℤ) : x ^ (∑ i ∈ s, b i) = ∏ i ∈ s, x ^ b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hx, ih]

/-- Integer exponent substitution is exact, including negative exponents. -/
theorem monomialBasis_relation {r k : ℕ} (α : Fin k → ℚ)
    (hα : ∀ j, α j ≠ 0) (v : Fin r → Fin k → ℤ) (b : Fin r → ℤ) :
    (∏ s, monomialBasis α v s ^ b s) = ∏ j, α j ^ integerCombination v b j := by
  calc
    (∏ s, monomialBasis α v s ^ b s) =
        ∏ s, ∏ j, α j ^ (b s * v s j) := by
      apply Finset.prod_congr rfl
      intro s _
      rw [monomialBasis, ← Finset.prod_zpow]
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_mul]
      congr 1
      exact mul_comm _ _
    _ = ∏ j, ∏ s, α j ^ (b s * v s j) := Finset.prod_comm
    _ = ∏ j, α j ^ integerCombination v b j := by
      apply Finset.prod_congr rfl
      intro j _
      exact (rational_zpow_sum Finset.univ (α j) (hα j) _).symm

/-- Injective integer coefficient changes preserve multiplicative independence. -/
theorem multiplicativelyIndependent_monomialBasis_of_injective {r k : ℕ}
    (α : Fin k → ℚ) (hα : ∀ j, α j ≠ 0)
    (hind : MultiplicativelyIndependent α) (v : Fin r → Fin k → ℤ)
    (hv : Function.Injective (integerCombination v)) :
    MultiplicativelyIndependent (monomialBasis α v) := by
  intro b hb
  apply hv
  rw [integerCombination_zero]
  apply hind
  rwa [← monomialBasis_relation α hα v b]

/-- Independent integer rows produce independent positive rational generators. -/
theorem multiplicativelyIndependent_monomialBasis {r k : ℕ}
    (α : Fin k → ℚ) (hα : ∀ j, 0 < α j)
    (hind : MultiplicativelyIndependent α) (v : Fin r → Fin k → ℤ)
    (hv : LinearIndependent ℤ v) :
    MultiplicativelyIndependent (monomialBasis α v) :=
  multiplicativelyIndependent_monomialBasis_of_injective α (fun j => (hα j).ne')
    hind v (integerCombination_injective v hv)

/-- The integer constant and the real value of a linear form survive basis change. -/
theorem linearForm_monomialBasis {r k : ℕ} (α : Fin k → ℚ)
    (hα : ∀ j, 0 < α j) (v : Fin r → Fin k → ℤ)
    (p : ℤ) (b : Fin r → ℤ) :
    linearForm (monomialBasis α v) p b = linearForm α p (integerCombination v b) := by
  unfold linearForm
  congr 1
  rw [← log_rational_monomial (monomialBasis α v) (monomialBasis_pos α hα v) b,
    monomialBasis_relation α (fun j => (hα j).ne') v b,
    log_rational_monomial α hα (integerCombination v b)]

/-- A deliberately simple positive size constant for an integer basis change. -/
def integerBasisSize {r k : ℕ} (v : Fin r → Fin k → ℤ) : ℕ :=
  1 + ∑ s, ∑ j, (v s j).natAbs

theorem one_le_integerBasisSize {r k : ℕ} (v : Fin r → Fin k → ℤ) :
    1 ≤ integerBasisSize v := by
  unfold integerBasisSize
  omega

/-- An explicit forward comparison for the coefficient height. This estimate
does not need independence of the rows. -/
theorem coefficientHeight_integerCombination_le {r k : ℕ}
    (v : Fin r → Fin k → ℤ) (p : ℤ) (b : Fin r → ℤ) :
    coefficientHeight p (integerCombination v b) ≤
      integerBasisSize v * coefficientHeight p b := by
  have hH : coefficientHeight p b ≤ integerBasisSize v * coefficientHeight p b := by
    simpa using Nat.mul_le_mul_right (coefficientHeight p b) (one_le_integerBasisSize v)
  have hcoord (j : Fin k) : (integerCombination v b j).natAbs ≤
      integerBasisSize v * coefficientHeight p b := by
    calc
      (integerCombination v b j).natAbs ≤ ∑ s, (b s * v s j).natAbs :=
        Int.natAbs_sum_le _ _
      _ = ∑ s, (b s).natAbs * (v s j).natAbs := by simp only [Int.natAbs_mul]
      _ ≤ ∑ s, coefficientHeight p b * (∑ t, (v s t).natAbs) := by
        apply Finset.sum_le_sum
        intro s _
        exact Nat.mul_le_mul (natAbs_coefficient_le_height p b s)
          (Finset.single_le_sum (f := fun t => (v s t).natAbs)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
      _ = coefficientHeight p b * (∑ s, ∑ t, (v s t).natAbs) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ coefficientHeight p b * integerBasisSize v := by
        apply Nat.mul_le_mul_left
        unfold integerBasisSize
        omega
      _ = integerBasisSize v * coefficientHeight p b := Nat.mul_comm _ _
  unfold coefficientHeight
  apply max_le
  · exact (two_le_coefficientHeight p b).trans hH
  · apply max_le
    · exact (natAbs_constant_le_height p b).trans hH
    · exact Finset.sup_le fun j _ => hcoord j

/-- info: 'GeneralizedLogarithms.multiplicativelyIndependent_monomialBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multiplicativelyIndependent_monomialBasis

/-- info: 'GeneralizedLogarithms.linearForm_monomialBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms linearForm_monomialBasis

/-- info: 'GeneralizedLogarithms.coefficientHeight_integerCombination_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coefficientHeight_integerCombination_le

end GeneralizedLogarithms
