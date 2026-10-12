import LogIrrationalityMeasure.Approximation.CoordinateSliceComparison
import LogIrrationalityMeasure.Jets.PrimeNormalCotangent
import LogIrrationalityMeasure.LocalAlgebra.WeightedBezoutBound

/-!
# Weighted prime length for an arbitrary finite coordinate type

The original prime-length wrapper restricts the ambient coordinates to `Fin n`.
Its slicing ingredients already support arbitrary finite coordinate types. This
wrapper uses those ingredients directly, so it applies to `Fin k ⊕ Fin m`
without transporting the ambient prime ideal or its residue field. The slice
itself is enumerated by `Fin A.card`, as required by the existing local Bezout
bound. The comparison retains the actual number of normal directions.
-/

namespace GeneralizedLogarithms
namespace FiniteVariableBezout

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open CoordinateFiniteSlice CoordinateSliceComparison NormalBasisRigidity WeightedSliceDegree

/-- A coordinate normal basis gives the weighted Bezout upper bound on the
localized length at a minimal prime, for any finite ambient coordinate type. -/
theorem weighted_prime_length_bound {ι : Type} [Fintype ι]
    (Q : Ideal (MvPolynomial ι ℂ)) [Q.IsPrime]
    (A : Finset ι)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    {J : Type*} (f : J → MvPolynomial ι ℂ)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : ι → ℚ) (hrho : ∀ i, 0 < rho i)
    (N : ℝ) (hN : 0 ≤ N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N) :
    ∃ L : ℕ, primeLength Q (Ideal.span (Set.range f)) = L ∧
      (L : ℝ) ≤ N ^ A.card / ∏ i ∈ A, (rho i : ℝ) := by
  classical
  let : Infinite Q.ResidueField := Infinite.of_injective
    (algebraMap ℂ Q.ResidueField) (algebraMap ℂ Q.ResidueField).injective
  have hminimal := sliceFamily_mem_minimalPrimes_of_normalBasis Q A hA f hQ
  have hlength := length_eq_sliceFamily_of_normalBasis Q A hA f
  have hrhoR (i : ι) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hsliceDegree : ∀ j, ∀ d ∈
      (enumeratedSliceMap A (residueCoordinates Q) (f j)).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho (A.equivFin.symm i) : ℝ)) ≤ N := by
    intro j
    exact supportBound_enumeratedSliceMap_sum A (residueCoordinates Q)
      (fun i => (rho i : ℝ)) (fun i => (hrhoR i).le) N (f j) (hdegree j)
  obtain ⟨L, hL, hupper⟩ := WeightedBezout.rational_pointLength_bound
    Q.ResidueField (fun j => enumeratedSliceMap A (residueCoordinates Q) (f j))
    (slicePoint Q A) (fun i => rho (A.equivFin.symm i)) (fun i => hrho _) N hN
    hsliceDegree hminimal
  refine ⟨L, hlength.trans hL, ?_⟩
  have hp : (∏ i : Fin A.card, (rho (A.equivFin.symm i) : ℝ)) =
      ∏ i ∈ A, (rho i : ℝ) := by
    calc
      _ = ∏ i : A, (rho i : ℝ) :=
        Fintype.prod_equiv A.equivFin.symm _ _ (fun _ => rfl)
      _ = _ := Finset.prod_coe_sort A (fun i => (rho i : ℝ))
  simpa only [hp] using hupper

end
end FiniteVariableBezout
end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.FiniteVariableBezout.weighted_prime_length_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.FiniteVariableBezout.weighted_prime_length_bound
