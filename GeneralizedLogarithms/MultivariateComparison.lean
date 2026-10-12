import GeneralizedLogarithms.FiniteVariableBezout
import GeneralizedLogarithms.MultivariateMultiplicity
import LogIrrationalityMeasure.Jets.TransverseWeightedMultiplicity
import LogIrrationalityMeasure.Jets.NormalBasisProducts

/-!
# The multivariate multiplicity comparison

Weighted degree and weighted derivative vanishing at a minimal prime give
the comparison between every coordinate normal basis and every logarithmic
frame normal basis. The constant is `c^c / epsilon^c`, where `c` is the
normal dimension, rather than an enlarged ambient-dimension constant.

The component and vanishing hypotheses still need to be obtained from a
persistent-component construction in the complete interpolation argument.
-/

namespace GeneralizedLogarithms.MultivariateComparison

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponentApprox
open NormalBasisRigidity TransverseWeightedMultiplicity
open MultivariatePolynomialFrame MultivariateMultiplicity

variable {k m : ℕ}

/-- One sufficiently large degree threshold works for every selection of at
most `b` frame directions in a fixed finite ambient set. -/
theorem eventually_uniform_rectangularCutoff_two_le {ι : Type*} [Fintype ι]
    (b : ℕ) (cost : ι → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ q : ℕ, 0 < q → q ≤ b →
      ∀ B : Fin q → ι, ∀ i,
        2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i := by
  have ht : Filter.Tendsto (fun N : ℝ => epsilon * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hepsilon
  have hb : ∀ᶠ N : ℝ in Filter.atTop, ∀ j : ι,
      (b : ℝ) * cost j < epsilon * N :=
    Filter.eventually_all.mpr (fun j =>
      ht.eventually (Filter.eventually_gt_atTop ((b : ℝ) * cost j)))
  filter_upwards [hb] with N hN
  intro q hq hqb B i
  have hdim : (q : ℝ) ≤ b := by exact_mod_cast hqb
  apply two_le_rectangularCutoff hq (fun j => cost (B j)) (fun j => hcost _) i
  exact (mul_le_mul_of_nonneg_right hdim (hcost _).le).trans_lt (hN (B i))

/-- Compare a coordinate normal basis with an enumerated frame normal basis.
Both local-length bounds are derived from the geometric input hypotheses. -/
theorem comparison_of_normal_basis
    (a : Fin m → Fin k → ℂ)
    (Q : Ideal (Polynomial ℂ k m)) [Q.IsPrime]
    (hy : ∀ r, primeResidueMap Q (MvPolynomial.X (Sum.inl r)) ≠ 0)
    (A : Finset (Fin k ⊕ Fin m)) (hc : 0 < A.card)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ j)) A)
    (B : Fin A.card → Fin k ⊕ Fin m)
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (MultivariateFrame.frameBasis
          (fun i r => primeResidueMap Q (MvPolynomial.C (a i r)))
          (fun r => primeResidueMap Q (MvPolynomial.X (Sum.inl r))) hy (B j))))
    {J : Type*} (f : J → Polynomial ℂ k m)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : (Fin k ⊕ Fin m) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : (Fin k ⊕ Fin m) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ i, 2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ word : List (Fin k ⊕ Fin m),
      wordCost cost word ≤ epsilon * N → frameWord a word p ∈ Q) :
    (∏ i ∈ A, (rho i : ℝ)) ≤
      (A.card : ℝ) ^ A.card * (∏ i, cost (B i)) / epsilon ^ A.card := by
  obtain ⟨L, hL, hupper⟩ := FiniteVariableBezout.weighted_prime_length_bound
    Q A hA f hQ rho hrho N hN.le hdegree
  have hlower := prime_frame_rectangular_length_lower a A.card Q hy B hB
    (Ideal.span (Set.range f)) cost
    (rectangularCutoff (fun j => cost (B j)) (epsilon * N)) (epsilon * N) hn
    (fun i => (hcost i).le)
    (rectangularCutoff_budget hc (fun j => cost (B j)) (fun j => hcost _)
      (epsilon * N) (mul_pos hepsilon hN)) hvanish
  change (∏ i, rectangularCutoff (fun j => cost (B j)) (epsilon * N) i : ℕ) ≤
    CoordinateSliceComparison.primeLength Q (Ideal.span (Set.range f)) at hlower
  rw [hL] at hlower
  have hrhoR (i : Fin k ⊕ Fin m) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have h := weight_comparison_of_rectangular_count hc
    (fun i => (rho (A.equivFin.symm i) : ℝ)) (fun j => cost (B j)) epsilon N L
    (fun i => hrhoR _) (fun j => hcost _) hepsilon hN (by exact_mod_cast hlower)
    (by simpa only [NormalBasisProducts.prod_equivFin A (fun i => (rho i : ℝ))] using hupper)
  simpa only [NormalBasisProducts.prod_equivFin A (fun i => (rho i : ℝ))] using h

/-- The product comparison for arbitrary pairs of normal bases. The cutoff
condition is uniform over selections of the same number of frame directions.
This is the universal comparison required by transverse rigidity. -/
theorem comparison_of_normal_bases
    (a : Fin m → Fin k → ℂ)
    (Q : Ideal (Polynomial ℂ k m)) [Q.IsPrime]
    (hy : ∀ r, primeResidueMap Q (MvPolynomial.X (Sum.inl r)) ≠ 0)
    (A B : Finset (Fin k ⊕ Fin m)) (hc : 0 < A.card)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ j)) A)
    (hB : IsNormalBasis (K := Q.ResidueField)
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (MultivariateFrame.frameBasis
          (fun i r => primeResidueMap Q (MvPolynomial.C (a i r)))
          (fun r => primeResidueMap Q (MvPolynomial.X (Sum.inl r))) hy j)) B)
    {J : Type*} (f : J → Polynomial ℂ k m)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : (Fin k ⊕ Fin m) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : (Fin k ⊕ Fin m) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ b : Fin A.card → Fin k ⊕ Fin m, ∀ i,
      2 ≤ rectangularCutoff (fun j => cost (b j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ word : List (Fin k ⊕ Fin m),
      wordCost cost word ≤ epsilon * N → frameWord a word p ∈ Q) :
    (∏ i ∈ A, (rho i : ℝ)) ≤
      ((A.card : ℝ) ^ A.card / epsilon ^ A.card) * ∏ i ∈ B, cost i := by
  classical
  have hcard : A.card = B.card := hA.card_eq.trans hB.card_eq.symm
  have h := comparison_of_normal_basis a Q hy A hc hA
    (NormalBasisProducts.enumeration A B hcard)
    (NormalBasisProducts.enumeration_linearIndependent A B hcard hB)
    f hQ rho hrho cost hcost epsilon N hepsilon hN hdegree (hn _) hvanish
  rw [NormalBasisProducts.prod_enumeration A B hcard cost] at h
  convert h using 1 <;> ring

end
end GeneralizedLogarithms.MultivariateComparison

/-- info: 'GeneralizedLogarithms.MultivariateComparison.comparison_of_normal_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateComparison.comparison_of_normal_basis

/-- info: 'GeneralizedLogarithms.MultivariateComparison.comparison_of_normal_bases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateComparison.comparison_of_normal_bases

/-- info: 'GeneralizedLogarithms.MultivariateComparison.eventually_uniform_rectangularCutoff_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateComparison.eventually_uniform_rectangularCutoff_two_le
