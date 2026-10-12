import GeneralizedLogarithms.MultivariatePersistence
import LogIrrationalityMeasure.Approximation.WeightedSliceDegree

/-!
# Weighted degrees of multivariate frame equations

Partial differentiation lowers the support bound by its coordinate weight;
multiplication by that coordinate restores the bound. Constant coefficients
do not increase it. Consequently every word in the multivariate logarithmic
frame preserves a weighted support bound for nonnegative weights, as does
every equation in a bounded derivative family.
-/

namespace GeneralizedLogarithms
namespace MultivariateDegree

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent.WeightedSliceDegree
open MultivariatePolynomialFrame MultivariateMultiplicity MultivariatePersistence

section PolynomialSupport

variable {C ι : Type*} [Field C]

theorem pderiv_support_shift (i : ι) (p : MvPolynomial ι C) (d : ι →₀ ℕ)
    (hd : d ∈ (MvPolynomial.pderiv i p).support) :
    d + Finsupp.single i 1 ∈ p.support := by
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  apply hcoeff
  rw [MvPolynomial.coeff_pderiv, hz, zero_mul]

/-- Differentiation lowers the support bound by the differentiated weight. -/
theorem supportBound_pderiv (W : ι → ℝ) (N : ℝ) (p : MvPolynomial ι C)
    (hp : SupportBound W N p) (i : ι) :
    SupportBound W (N - W i) (MvPolynomial.pderiv i p) := by
  intro d hd
  apply (le_sub_iff_add_le).mpr
  have h := hp (d + Finsupp.single i 1) (pderiv_support_shift i p d hd)
  simpa only [map_add, Finsupp.weight_single, one_nsmul] using h

/-- A nonnegative coordinate weight makes differentiation bound-preserving. -/
theorem supportBound_pderiv_preserves (W : ι → ℝ) (N : ℝ) (p : MvPolynomial ι C)
    (hp : SupportBound W N p) (i : ι) (hi : 0 ≤ W i) :
    SupportBound W N (MvPolynomial.pderiv i p) :=
  (supportBound_pderiv W N p hp i).mono (sub_le_self N hi)

/-- Constant polynomial coefficients do not increase the weighted bound. -/
theorem supportBound_C_mul (W : ι → ℝ) (N : ℝ) (p : MvPolynomial ι C)
    (hp : SupportBound W N p) (c : C) :
    SupportBound W N (MvPolynomial.C c * p) := by
  simpa only [zero_add] using (supportBound_C W c).mul hp

/-- The Euler operator preserves the weighted support bound without a sign
restriction on the weight of this coordinate. -/
theorem supportBound_X_mul_pderiv (W : ι → ℝ) (N : ℝ) (p : MvPolynomial ι C)
    (hp : SupportBound W N p) (i : ι) :
    SupportBound W N (MvPolynomial.X i * MvPolynomial.pderiv i p) := by
  have h := (supportBound_X (E := C) W i).mul (supportBound_pderiv W N p hp i)
  have hN : W i + (N - W i) = N := by ring
  simpa only [hN] using h

end PolynomialSupport

variable {C : Type*} [Field C] {k m : ℕ}

/-- Every longitudinal logarithmic operator preserves the weighted bound. -/
theorem supportBound_logarithmicDerivation (a : Fin m → Fin k → C)
    (W : (Fin k ⊕ Fin m) → ℝ) (N : ℝ) (p : Polynomial C k m)
    (hp : SupportBound W N p) (hW : ∀ j, 0 ≤ W j) (r : Fin k) :
    SupportBound W N (logarithmicDerivation a r p) := by
  rw [logarithmicDerivation_apply]
  apply (supportBound_X_mul_pderiv W N p hp (Sum.inl r)).add
  apply supportBound_sum Finset.univ W _ N
  intro i _
  exact supportBound_C_mul W N _
    (supportBound_pderiv_preserves W N p hp (Sum.inr i) (hW _)) (a i r)

/-- Every operator in the complete frame preserves the weighted bound. -/
theorem supportBound_polynomialFrame (a : Fin m → Fin k → C)
    (W : (Fin k ⊕ Fin m) → ℝ) (N : ℝ) (p : Polynomial C k m)
    (hp : SupportBound W N p) (hW : ∀ j, 0 ≤ W j) (j : Fin k ⊕ Fin m) :
    SupportBound W N (polynomialFrame a j p) := by
  cases j with
  | inl r => exact supportBound_logarithmicDerivation a W N p hp hW r
  | inr i => exact supportBound_pderiv_preserves W N p hp (Sum.inr i) (hW _)

variable [CharZero C]

/-- Arbitrarily long frame words preserve the initial weighted support bound. -/
theorem supportBound_frameWord (a : Fin m → Fin k → C)
    (W : (Fin k ⊕ Fin m) → ℝ) (N : ℝ) (p : Polynomial C k m)
    (hp : SupportBound W N p) (hW : ∀ j, 0 ≤ W j)
    (word : List (Fin k ⊕ Fin m)) : SupportBound W N (frameWord a word p) := by
  induction word with
  | nil => exact hp
  | cons j word ih =>
    change SupportBound W N (polynomialFrame a j (frameWord a word p))
    exact supportBound_polynomialFrame a W N _ ih hW j

/-- Every equation generating a bounded derivative ideal has the same support
bound as the starting polynomial. -/
theorem equation_supportBound (a : Fin m → Fin k → C)
    (cost W : (Fin k ⊕ Fin m) → ℝ) (bound N : ℝ) (F : Polynomial C k m)
    (hF : SupportBound W N F) (hW : ∀ j, 0 ≤ W j)
    (word : BoundedWords cost bound) : SupportBound W N (equations a cost bound F word) :=
  supportBound_frameWord a W N F hF hW word.val

/-- Explicit exponent-sum form of the equation support bound, matching the
input expected by the weighted prime Bezout theorem. -/
theorem equation_weighted_sum_le (a : Fin m → Fin k → C)
    (cost W : (Fin k ⊕ Fin m) → ℝ) (bound N : ℝ) (F : Polynomial C k m)
    (hF : SupportBound W N F) (hW : ∀ j, 0 ≤ W j)
    (word : BoundedWords cost bound) :
    ∀ d ∈ (equations a cost bound F word).support,
      (∑ j ∈ d.support, (d j : ℝ) * W j) ≤ N := by
  have h := equation_supportBound a cost W bound N F hF hW word
  simpa only [SupportBound, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using h

end
end MultivariateDegree
end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.MultivariateDegree.supportBound_X_mul_pderiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateDegree.supportBound_X_mul_pderiv

/-- info: 'GeneralizedLogarithms.MultivariateDegree.supportBound_frameWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateDegree.supportBound_frameWord

/-- info: 'GeneralizedLogarithms.MultivariateDegree.equation_weighted_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateDegree.equation_weighted_sum_le
