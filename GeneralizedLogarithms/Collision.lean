import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Capacity bounds for multivariate determinant collisions

The Taylor degree alone need not distinguish rows in several variables. The
complete mode does: a repeated mode gives equal coefficient rows, so its
determinant vanishes. A finite capacity bound on the modes of small degree then
forces a lower bound on the sum of all Taylor degrees.

This file proves that finite combinatorial step. The asymptotic count of the
capacity set and convergence of the infinite determinant expansion are separate
obligations; they are not asserted here.
-/

namespace GeneralizedLogarithms

open scoped BigOperators

section Determinant

variable {ι μ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A nonzero determinant of coefficient rows uses distinct complete modes. -/
theorem coefficient_mode_injective_of_det_ne_zero
    (mode : ι → μ) (coefficient : μ → ι → R)
    (hdet : Matrix.det (fun i j => coefficient (mode i) j) ≠ 0) :
    Function.Injective mode := by
  intro i j hij
  by_contra hne
  apply hdet
  apply Matrix.det_zero_of_row_eq hne
  funext l
  rw [hij]

/-- Row-dependent evaluation or translation scalars do not avoid collision
cancellation. Factor them out of the determinant before testing equal modes. -/
theorem scaled_coefficient_mode_injective_of_det_ne_zero
    (mode : ι → μ) (coefficient : μ → ι → R) (scalar : ι → R)
    (hdet : Matrix.det (fun i j => scalar i * coefficient (mode i) j) ≠ 0) :
    Function.Injective mode := by
  apply coefficient_mode_injective_of_det_ne_zero mode coefficient
  intro hz
  apply hdet
  calc
    Matrix.det (fun i j => scalar i * coefficient (mode i) j) =
        (∏ i, scalar i) * Matrix.det (fun i j => coefficient (mode i) j) :=
      Matrix.det_mul_column scalar (fun i j => coefficient (mode i) j)
    _ = 0 := by rw [hz, mul_zero]

end Determinant

section Capacity

variable {ι μ : Type*}

/-- If every small-degree mode on a selected row belongs to a finite capacity
set, injectivity forces at least `selected.card - capacity.card` rows to have
degree at least the cutoff. Degrees on the other rows only need to be nonnegative.
-/
theorem degree_sum_ge_capacity_deficit
    (rows : Finset ι) (selected : ι → Prop) [DecidablePred selected]
    (mode : ι → μ) (degree : μ → ℝ) (capacity : Finset μ) (cutoff : ℝ)
    (hcutoff : 0 ≤ cutoff)
    (hinj : Set.InjOn mode (rows : Set ι))
    (hnonneg : ∀ i ∈ rows, 0 ≤ degree (mode i))
    (hcover : ∀ i ∈ rows, selected i → degree (mode i) < cutoff →
      mode i ∈ capacity) :
    (((rows.filter selected).card : ℝ) - capacity.card) * cutoff ≤
      ∑ i ∈ rows, degree (mode i) := by
  classical
  let chosen := rows.filter selected
  let small := chosen.filter (fun i => degree (mode i) < cutoff)
  let large := chosen.filter (fun i => ¬ degree (mode i) < cutoff)
  have hsmall : small.card ≤ capacity.card := by
    apply Finset.card_le_card_of_injOn mode
    · intro i hi
      have his := Finset.mem_filter.mp hi
      have hic := Finset.mem_filter.mp his.1
      exact hcover i hic.1 hic.2 his.2
    · intro i hi j hj hij
      exact hinj (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1 hij
  have hpartition : small.card + large.card = chosen.card :=
    Finset.card_filter_add_card_filter_not (s := chosen)
      (fun i => degree (mode i) < cutoff)
  have hpartition_real : (small.card : ℝ) + large.card = chosen.card := by
    simpa only [Nat.cast_add] using
      congrArg (fun n : ℕ => (n : ℝ)) hpartition
  have hsmall_real : (small.card : ℝ) ≤ capacity.card := Nat.cast_le.mpr hsmall
  have hlarge : (chosen.card : ℝ) - capacity.card ≤ large.card := by
    linarith
  have hlarge_subset : large ⊆ rows := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  calc
    (((rows.filter selected).card : ℝ) - capacity.card) * cutoff ≤
        (large.card : ℝ) * cutoff :=
      mul_le_mul_of_nonneg_right hlarge hcutoff
    _ = ∑ _i ∈ large, cutoff := by simp
    _ ≤ ∑ i ∈ large, degree (mode i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_not_gt (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ rows, degree (mode i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hlarge_subset
      intro i hi _
      exact hnonneg i hi

/-- The collision saving used in the proposed argument: at least `η M`
selected rows and at most `η M / 2` small modes imply a total degree of at least
`η M S H / 2`. The selected rows will be the rows of small transverse weight. -/
theorem collision_degree_sum_lower_bound
    (rows : Finset ι) (selected : ι → Prop) [DecidablePred selected]
    (mode : ι → μ) (degree : μ → ℝ) (capacity : Finset μ) (η S H : ℝ)
    (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hinj : Set.InjOn mode (rows : Set ι))
    (hnonneg : ∀ i ∈ rows, 0 ≤ degree (mode i))
    (hcover : ∀ i ∈ rows, selected i → degree (mode i) < S * H →
      mode i ∈ capacity)
    (hselected : η * rows.card ≤ ((rows.filter selected).card : ℝ))
    (hcapacity : (capacity.card : ℝ) ≤ η * rows.card / 2) :
    η * rows.card * S * H / 2 ≤ ∑ i ∈ rows, degree (mode i) := by
  have hcount : η * rows.card / 2 ≤
      ((rows.filter selected).card : ℝ) - capacity.card := by
    linarith
  calc
    η * rows.card * S * H / 2 = (η * rows.card / 2) * (S * H) := by ring
    _ ≤ (((rows.filter selected).card : ℝ) - capacity.card) * (S * H) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hS hH)
    _ ≤ ∑ i ∈ rows, degree (mode i) :=
      degree_sum_ge_capacity_deficit rows selected mode degree capacity (S * H)
        (mul_nonneg hS hH) hinj hnonneg hcover

end Capacity

/-- A concrete multivariate version for modes `(γ,d)`, with `d : Fin k → ℕ`.
Injectivity is a conclusion of the nonvanishing coefficient determinant. The
capacity hypothesis is precisely where the lattice-point estimate enters.
-/
theorem multivariate_collision_degree_sum_lower_bound
    {ι Γ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] {k : ℕ}
    (mode : ι → Γ × (Fin k → ℕ))
    (transverseLow : Γ → Prop) [DecidablePred transverseLow]
    (coefficient : Γ × (Fin k → ℕ) → ι → R) (scalar : ι → R)
    (capacity : Finset (Γ × (Fin k → ℕ))) (η S H : ℝ)
    (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hdet : Matrix.det (fun i j => scalar i * coefficient (mode i) j) ≠ 0)
    (hcover : ∀ γ d, transverseLow γ →
      (∑ r, (d r : ℝ)) < S * H → (γ, d) ∈ capacity)
    (hselected : η * Fintype.card ι ≤
      ((Finset.univ.filter fun i => transverseLow (mode i).1).card : ℝ))
    (hcapacity : (capacity.card : ℝ) ≤ η * Fintype.card ι / 2) :
    η * Fintype.card ι * S * H / 2 ≤ ∑ i, ∑ r, ((mode i).2 r : ℝ) := by
  have hinj := scaled_coefficient_mode_injective_of_det_ne_zero
    mode coefficient scalar hdet
  apply collision_degree_sum_lower_bound Finset.univ
    (fun i => transverseLow (mode i).1) mode
    (fun p => ∑ r, (p.2 r : ℝ)) capacity η S H hS hH hinj.injOn
  · intro i _
    exact Finset.sum_nonneg fun r _ => Nat.cast_nonneg _
  · intro i _ hi hd
    exact hcover (mode i).1 (mode i).2 hi hd
  · simpa using hselected
  · simpa using hcapacity

end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.coefficient_mode_injective_of_det_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.coefficient_mode_injective_of_det_ne_zero

/-- info: 'GeneralizedLogarithms.scaled_coefficient_mode_injective_of_det_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.scaled_coefficient_mode_injective_of_det_ne_zero

/-- info: 'GeneralizedLogarithms.collision_degree_sum_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.collision_degree_sum_lower_bound

/-- info: 'GeneralizedLogarithms.multivariate_collision_degree_sum_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.multivariate_collision_degree_sum_lower_bound
