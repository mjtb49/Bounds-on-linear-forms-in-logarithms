import GeneralizedLogarithms.MultivariateFrame
import GeneralizedLogarithms.MonomialDifferential
import GeneralizedLogarithms.GenericConormal
import LogIrrationalityMeasure.Jets.PrimeNormalCotangent

/-!
# The polynomial tangent space of a persistent prime component

The multiplicity estimates in the original repository use `polynomialTangent`,
the kernel of the Jacobian of the prime ideal. This file applies the new frame
directly to that tangent space. Every function-field derivation gives a vector
in this kernel. Conversely, a coordinate that is constant in the residue field
has a linear defining equation in the prime ideal, so its coordinate vanishes
on every polynomial tangent vector.

This is sufficient for both constancy and the strict codimension estimate; no
identification with the span of all derivation vectors is assumed. Universal
multiplicity comparison and weight separation remain explicit hypotheses.
-/

namespace GeneralizedLogarithms
namespace PolynomialPrimeAdapter

noncomputable section

open scoped BigOperators
open MvPolynomial
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponent.NormalBasisRigidity

variable {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C]
  [Field E] [Algebra C E] {k m : ℕ}

/-- The coordinate normal family used by the existing multiplicity estimates. -/
def coordinateNormalFamily
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C)) (j : Fin k ⊕ Fin m) :=
  (polynomialTangent φ Q).mkQ (Pi.basisFun E _ j)

/-- The new logarithmic frame in that same polynomial normal quotient. -/
def frameNormalFamily
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (a : Fin m → Fin k → ℤ) (hy : ∀ r : Fin k, φ (X (Sum.inl r)) ≠ 0)
    (j : Fin k ⊕ Fin m) :=
  (polynomialTangent φ Q).mkQ
    (MultivariateFrame.frameBasis (fun i r => (a i r : E))
      (fun r => φ (X (Sum.inl r))) hy j)

omit [CharZero C] [IsAlgClosed C] in
/-- An equality in the function field gives the corresponding coordinate
equation in the defining ideal when that ideal is the exact kernel. -/
theorem coordinate_sub_constant_mem
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q)
    (j : Fin k ⊕ Fin m) (c : C) (hc : algebraMap C E c = φ (X j)) :
    X j - MvPolynomial.C c ∈ Q := by
  apply (hker _).mp
  simp only [map_sub, MvPolynomial.algHom_C, hc, sub_self]

omit [CharZero C] [IsAlgClosed C] in
/-- A residue-constant coordinate vanishes on all polynomial tangent vectors.
This uses the linear equation in `Q`, not a converse theorem about derivations. -/
theorem tangent_coordinate_eq_zero_of_constant
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q)
    (j : Fin k ⊕ Fin m) (hc : ∃ c : C, algebraMap C E c = φ (X j))
    (t : (Fin k ⊕ Fin m) → E) (ht : t ∈ polynomialTangent φ Q) : t j = 0 := by
  obtain ⟨c, hc⟩ := hc
  have hp := coordinate_sub_constant_mem φ Q hker j c hc
  change polynomialJacobian φ Q t = 0 at ht
  have h := congrFun ht ⟨X j - MvPolynomial.C c, hp⟩
  cases j <;> simpa [polynomialJacobian, Pi.single_apply] using h

variable [Algebra.EssFiniteType C E]

/-- A mandatory column in the polynomial normal quotient forces constancy of
its transverse coordinate and of its associated Laurent monomial. -/
theorem constants_of_mandatory_normal_direction
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hvan : ∀ p ∈ Q, φ p = 0)
    (a : Fin m → Fin k → ℤ) (hy : ∀ r : Fin k, φ (X (Sum.inl r)) ≠ 0)
    (i : Fin m)
    (hi : ∀ B, IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B → Sum.inr i ∈ B) :
    (∃ c : C, algebraMap C E c = ∏ r, φ (X (Sum.inl r)) ^ a i r) ∧
      ∃ b : C, algebraMap C E b = φ (X (Sum.inr i)) := by
  apply constants_of_monomial_derivation_relation Finset.univ
    (fun r => φ (X (Sum.inl r))) hy (a i) (φ (X (Sum.inr i)))
  intro δ
  exact MultivariateFrame.tangent_subspace_logarithmic_relation
    (fun i r => (a i r : E)) (fun r => φ (X (Sum.inl r))) hy
    (polynomialTangent φ Q) i hi (fun j => δ (φ (X j)))
    (derivation_mem_polynomialTangent φ Q hvan δ)

/-- Distinct mandatory directions and a nonzero selected integer row give the
strict codimension gap in the actual polynomial normal quotient. -/
theorem mandatory_directions_codimension_gap
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q)
    {I : Type*} [Fintype I] (e : I ↪ Fin m) (i₀ : I)
    (a : Fin m → Fin k → ℤ) (hy : ∀ r : Fin k, φ (X (Sum.inl r)) ≠ 0)
    (ha : a (e i₀) ≠ 0)
    (hmandatory : ∀ i : I, ∀ B,
      IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B → Sum.inr (e i) ∈ B) :
    Fintype.card I + 1 ≤ Module.finrank E (PolynomialNormal φ Q) := by
  let : CharZero E := Algebra.charZero_of_charZero C E
  have hconstant : ∀ i : I, ∃ c : C, algebraMap C E c = φ (X (Sum.inr (e i))) := fun i =>
    (constants_of_mandatory_normal_direction φ Q (fun p hp => (hker p).mpr hp)
      a hy (e i) (hmandatory i)).2
  apply GenericConormal.coordinate_card_add_one_le_of_logarithmic_relation
    (polynomialTangent φ Q) e i₀ (a (e i₀)) ha (fun r => φ (X (Sum.inl r))) hy
  · intro i t ht
    exact tangent_coordinate_eq_zero_of_constant φ Q hker (Sum.inr (e i)) (hconstant i) t ht
  · intro t ht
    exact MultivariateFrame.tangent_subspace_logarithmic_relation
      (fun i r => (a i r : E)) (fun r => φ (X (Sum.inl r))) hy
      (polynomialTangent φ Q) (e i₀) (hmandatory i₀) t ht

/-- The comparison and separation hypotheses supplied by the geometric argument
force a common transverse set and residue-constant coordinates on the prime. -/
theorem weighted_polynomial_constancy [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (φ : MvPolynomial (Fin k ⊕ Fin m) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q)
    (a : Fin m → Fin k → ℤ) (hy : ∀ r : Fin k, φ (X (Sum.inl r)) ≠ 0)
    (w cost : (Fin k ⊕ Fin m) → ℝ) (bound : ℕ → ℝ)
    (hcomparison : ∀ A B,
      IsNormalBasis (K := E) (coordinateNormalFamily φ Q) A →
      IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B →
      (∏ j ∈ A, w j) ≤ bound A.card * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
      (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
        (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
      bound A.card * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ I : Finset (Fin k ⊕ Fin m),
      IsGreedyBasis (K := E) (coordinateNormalFamily φ Q) (Finset.univ.image Sum.inr) I ∧
      (∀ B, IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B →
        B ∩ Finset.univ.image Sum.inr = I) ∧
      ∀ i : Fin m, Sum.inr i ∈ I →
        (∃ c : C, algebraMap C E c = ∏ r, φ (X (Sum.inl r)) ^ a i r) ∧
        ∃ b : C, X (Sum.inr i) - MvPolynomial.C b ∈ Q := by
  obtain ⟨I, hI, hfixed, _⟩ := MultivariateFrame.weighted_tangent_relations
    (fun i r => (a i r : E)) (fun r => φ (X (Sum.inl r))) hy
    (polynomialTangent φ Q) w cost bound hcomparison hseparated
  refine ⟨I, hI, hfixed, ?_⟩
  intro i hi
  have hmand : ∀ B, IsNormalBasis (K := E) (frameNormalFamily φ Q a hy) B →
      Sum.inr i ∈ B := by
    intro B hB
    have himem : Sum.inr i ∈ B ∩ Finset.univ.image Sum.inr := by rw [hfixed B hB]; exact hi
    exact (Finset.mem_inter.mp himem).1
  obtain ⟨hm, b, hb⟩ := constants_of_mandatory_normal_direction φ Q
    (fun p hp => (hker p).mpr hp) a hy i hmand
  exact ⟨hm, b, coordinate_sub_constant_mem φ Q hker (Sum.inr i) b hb⟩

/-- Specialization to the residue field and prime map used by the original
local multiplicity estimates. -/
theorem prime_constants_of_mandatory_normal_direction
    (Q : Ideal (MvPolynomial (Fin k ⊕ Fin m) C)) [Q.IsPrime]
    (a : Fin m → Fin k → ℤ)
    (hy : ∀ r : Fin k, primeResidueMap Q (X (Sum.inl r)) ≠ 0)
    (i : Fin m)
    (hi : ∀ B, IsNormalBasis (K := Q.ResidueField)
      (frameNormalFamily (primeResidueMap Q) Q a hy) B → Sum.inr i ∈ B) :
    (∃ c : C, algebraMap C Q.ResidueField c = ∏ r, primeResidueMap Q (X (Sum.inl r)) ^ a i r) ∧
      ∃ b : C, X (Sum.inr i) - MvPolynomial.C b ∈ Q := by
  let : Algebra.EssFiniteType C Q.ResidueField :=
    Algebra.EssFiniteType.comp C (MvPolynomial (Fin k ⊕ Fin m) C) Q.ResidueField
  have hker (p : MvPolynomial (Fin k ⊕ Fin m) C) : primeResidueMap Q p = 0 ↔ p ∈ Q :=
    Ideal.algebraMap_residueField_eq_zero
  obtain ⟨hm, b, hb⟩ := constants_of_mandatory_normal_direction (primeResidueMap Q) Q
    (fun p hp => (hker p).mpr hp) a hy i hi
  exact ⟨hm, b, coordinate_sub_constant_mem (primeResidueMap Q) Q hker (Sum.inr i) b hb⟩

end
end PolynomialPrimeAdapter
end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.PolynomialPrimeAdapter.tangent_coordinate_eq_zero_of_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.PolynomialPrimeAdapter.tangent_coordinate_eq_zero_of_constant

/-- info: 'GeneralizedLogarithms.PolynomialPrimeAdapter.constants_of_mandatory_normal_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.PolynomialPrimeAdapter.constants_of_mandatory_normal_direction

/-- info: 'GeneralizedLogarithms.PolynomialPrimeAdapter.mandatory_directions_codimension_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.PolynomialPrimeAdapter.mandatory_directions_codimension_gap

/-- info: 'GeneralizedLogarithms.PolynomialPrimeAdapter.weighted_polynomial_constancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.PolynomialPrimeAdapter.weighted_polynomial_constancy

/-- info: 'GeneralizedLogarithms.PolynomialPrimeAdapter.prime_constants_of_mandatory_normal_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.PolynomialPrimeAdapter.prime_constants_of_mandatory_normal_direction
