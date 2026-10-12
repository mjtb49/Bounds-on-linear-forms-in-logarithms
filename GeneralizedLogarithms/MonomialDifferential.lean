import LogIrrationalityMeasure.Analysis.AlgebraicLogarithmicObstruction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Laurent monomials and logarithmic differentials

For a finite family of nonzero field elements, the logarithmic differential of
an integer monomial is the corresponding integer linear combination of their
logarithmic differentials.  The existing algebraic logarithmic obstruction
then makes both the monomial and an additive primitive constant over an
algebraically closed field of characteristic zero.

These statements concern the function field of a prospective subvariety.
The geometric step producing their differential hypotheses is separate.
-/

namespace GeneralizedLogarithms

open scoped BigOperators
open KaehlerDifferential

noncomputable section

section Derivation

variable {C E V : Type*} [CommRing C] [Field E] [Algebra C E]
  [AddCommGroup V] [Module E V] [Module C V]

/-- The product rule for logarithmic derivatives, with values in any module. -/
theorem logarithmic_derivation_mul (d : Derivation C E V) (u v : E)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (u * v)⁻¹ • d (u * v) = u⁻¹ • d u + v⁻¹ • d v := by
  have h₁ : (u * v)⁻¹ * u = v⁻¹ := by
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hu, mul_one]
  have h₂ : (u * v)⁻¹ * v = u⁻¹ := by
    rw [mul_comm u v, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hv, mul_one]
  rw [d.leibniz, smul_add, smul_smul, smul_smul, h₁, h₂, add_comm]

/-- The logarithmic derivative of an integer power, including negative powers. -/
theorem logarithmic_derivation_zpow (d : Derivation C E V) (y : E)
    (hy : y ≠ 0) (a : ℤ) :
    (y ^ a)⁻¹ • d (y ^ a) = (a : E) • (y⁻¹ • d y) := by
  have hpow : (y ^ a)⁻¹ * y ^ (a - 1) = y⁻¹ := by
    rw [zpow_sub₀ hy, zpow_one, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ (zpow_ne_zero a hy), one_mul]
  calc
    (y ^ a)⁻¹ • d (y ^ a) =
        ((y ^ a)⁻¹ * ((a : E) * y ^ (a - 1))) • d y := by
      rw [d.leibniz_zpow, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul]
      rw [mul_assoc]
    _ = ((a : E) * y⁻¹) • d y := by rw [mul_left_comm, hpow]
    _ = (a : E) • (y⁻¹ • d y) := by rw [smul_smul]

/-- The logarithmic derivative of a finite product of nonzero elements. -/
theorem logarithmic_derivation_prod {ι : Type*} (d : Derivation C E V)
    (s : Finset ι) (y : ι → E) (hy : ∀ i, y i ≠ 0) :
    (∏ i ∈ s, y i)⁻¹ • d (∏ i ∈ s, y i) =
      ∑ i ∈ s, (y i)⁻¹ • d (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.prod_insert his, Finset.sum_insert his,
        logarithmic_derivation_mul d _ _ (hy i)
          (Finset.prod_ne_zero_iff.mpr (fun j _ => hy j)), ih]

/-- The logarithmic differential of a finite Laurent monomial. -/
theorem logarithmic_derivation_monomial {ι : Type*} (d : Derivation C E V)
    (s : Finset ι) (y : ι → E) (hy : ∀ i, y i ≠ 0) (a : ι → ℤ) :
    (∏ i ∈ s, y i ^ a i)⁻¹ • d (∏ i ∈ s, y i ^ a i) =
      ∑ i ∈ s, (a i : E) • ((y i)⁻¹ • d (y i)) := by
  rw [logarithmic_derivation_prod d s (fun i => y i ^ a i)
    (fun i => zpow_ne_zero (a i) (hy i))]
  exact Finset.sum_congr rfl (fun i _ => logarithmic_derivation_zpow d (y i) (hy i) (a i))

end Derivation

section Constants

variable {C E ι : Type*} [Field C] [CharZero C] [IsAlgClosed C]
  [Field E] [Algebra C E] [Algebra.EssFiniteType C E]

omit [CharZero C] [IsAlgClosed C] in
/-- Testing all scalar-valued derivations detects the Kähler differential relation.
No finite-dimensionality assumption on the differential module is needed. -/
theorem kahler_relation_of_forall_derivation
    (s : Finset ι) (y : ι → E) (a : ι → ℤ) (x : E)
    (h : ∀ δ : Derivation C E E,
      δ x = ∑ i ∈ s, (a i : E) * (δ (y i) / y i)) :
    D C E x = ∑ i ∈ s, (a i : E) • ((y i)⁻¹ • D C E (y i)) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro φ
  have hφ : φ (D C E x) = ∑ i ∈ s, (a i : E) * (φ (D C E (y i)) / y i) :=
    h (φ.compDer (D C E))
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  apply sub_eq_zero.mpr
  simpa only [div_eq_mul_inv, mul_comm] using hφ

/-- A logarithmic relation makes its Laurent monomial constant in the function field. -/
theorem monomial_constant_of_differential_relation
    (s : Finset ι) (y : ι → E) (hy : ∀ i, y i ≠ 0) (a : ι → ℤ) (x : E)
    (h : D C E x = ∑ i ∈ s, (a i : E) • ((y i)⁻¹ • D C E (y i))) :
    ∃ c : C, algebraMap C E c = ∏ i ∈ s, y i ^ a i := by
  apply LogIrrationalityMeasure.LogExponent.constant_of_logarithmic_differential x
  rw [logarithmic_derivation_monomial (D C E) s y hy a]
  exact h

/-- The same relation forces the additive coordinate to have zero differential. -/
theorem differential_eq_zero_of_monomial_relation
    (s : Finset ι) (y : ι → E) (hy : ∀ i, y i ≠ 0) (a : ι → ℤ) (x : E)
    (h : D C E x = ∑ i ∈ s, (a i : E) • ((y i)⁻¹ • D C E (y i))) :
    D C E x = 0 := by
  obtain ⟨c, hc⟩ := monomial_constant_of_differential_relation s y hy a x h
  rw [← logarithmic_derivation_monomial (D C E) s y hy a, ← hc] at h
  simpa using h

/-- Both coordinates are constant; constancy of `x` is derived rather than assumed. -/
theorem constants_of_monomial_differential_relation
    (s : Finset ι) (y : ι → E) (hy : ∀ i, y i ≠ 0) (a : ι → ℤ) (x : E)
    (h : D C E x = ∑ i ∈ s, (a i : E) • ((y i)⁻¹ • D C E (y i))) :
    (∃ c : C, algebraMap C E c = ∏ i ∈ s, y i ^ a i) ∧
      ∃ b : C, algebraMap C E b = x := by
  refine ⟨monomial_constant_of_differential_relation s y hy a x h, ?_⟩
  have hx := differential_eq_zero_of_monomial_relation s y hy a x h
  exact LogIrrationalityMeasure.LogExponent.constant_of_logarithmic_differential
    (0 : E) x (by simp [hx])

/-- A logarithmic identity for every function-field derivation makes both the
Laurent monomial and the additive coordinate constant. -/
theorem constants_of_monomial_derivation_relation
    (s : Finset ι) (y : ι → E) (hy : ∀ i, y i ≠ 0) (a : ι → ℤ) (x : E)
    (h : ∀ δ : Derivation C E E,
      δ x = ∑ i ∈ s, (a i : E) * (δ (y i) / y i)) :
    (∃ c : C, algebraMap C E c = ∏ i ∈ s, y i ^ a i) ∧
      ∃ b : C, algebraMap C E b = x :=
  constants_of_monomial_differential_relation s y hy a x
    (kahler_relation_of_forall_derivation s y a x h)

end Constants

/-- info: 'GeneralizedLogarithms.logarithmic_derivation_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms logarithmic_derivation_monomial

/-- info: 'GeneralizedLogarithms.kahler_relation_of_forall_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kahler_relation_of_forall_derivation

/-- info: 'GeneralizedLogarithms.differential_eq_zero_of_monomial_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differential_eq_zero_of_monomial_relation

/-- info: 'GeneralizedLogarithms.constants_of_monomial_differential_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms constants_of_monomial_differential_relation

/-- info: 'GeneralizedLogarithms.constants_of_monomial_derivation_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms constants_of_monomial_derivation_relation

end

end GeneralizedLogarithms
