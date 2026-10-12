import GeneralizedLogarithms.MultivariateComparison
import GeneralizedLogarithms.PolynomialPrimeAdapter

/-!
# Constancy from weighted degree and local derivative vanishing

This file composes the actual local multiplicity estimates with transverse
normal-basis rigidity. It derives the universal basis comparison from weighted
degree bounds and derivative-word vanishing at a minimal prime, then obtains
constant monomials and transverse coordinate equations.

The existence of the persistent ideal and prime, and the numerical selection
of weights satisfying directed separation, remain explicit obligations.
-/

namespace GeneralizedLogarithms.GeometricConstancy

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponentApprox
open NormalBasisRigidity
open MultivariatePolynomialFrame MultivariateMultiplicity
open PolynomialPrimeAdapter

variable {k m : ℕ}

/-- The basis comparison derived from the two local multiplicity bounds,
including the zero-dimensional normal quotient. -/
theorem universal_comparison_of_weighted_vanishing
    (a : Fin m → Fin k → ℤ)
    (Q : Ideal (Polynomial ℂ k m)) [Q.IsPrime]
    (hy : ∀ r, primeResidueMap Q (MvPolynomial.X (Sum.inl r)) ≠ 0)
    {J : Type*} (f : J → Polynomial ℂ k m)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : (Fin k ⊕ Fin m) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : (Fin k ⊕ Fin m) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ q : ℕ, 0 < q → q ≤ k + m →
      ∀ B : Fin q → Fin k ⊕ Fin m, ∀ i,
        2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ word : List (Fin k ⊕ Fin m),
      wordCost cost word ≤ epsilon * N → frameWord (fun i r => (a i r : ℂ)) word p ∈ Q) :
    ∀ A B,
      IsNormalBasis (K := Q.ResidueField) (coordinateNormalFamily (primeResidueMap Q) Q) A →
      IsNormalBasis (K := Q.ResidueField) (frameNormalFamily (primeResidueMap Q) Q a hy) B →
      (∏ i ∈ A, (rho i : ℝ)) ≤
        ((A.card : ℝ) ^ A.card / epsilon ^ A.card) * ∏ i ∈ B, cost i := by
  classical
  intro A B hA hB
  by_cases hc : 0 < A.card
  · have hdim : A.card ≤ k + m := by
      simpa only [Fintype.card_sum, Fintype.card_fin] using Finset.card_le_univ A
    have hB' : IsNormalBasis (K := Q.ResidueField)
        (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
          (MultivariateFrame.frameBasis
            (fun i r => primeResidueMap Q (MvPolynomial.C (a i r : ℂ)))
            (fun r => primeResidueMap Q (MvPolynomial.X (Sum.inl r))) hy j)) B := by
      change IsNormalBasis (K := Q.ResidueField)
        (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
          (MultivariateFrame.frameBasis (fun i r => (a i r : Q.ResidueField))
            (fun r => primeResidueMap Q (MvPolynomial.X (Sum.inl r))) hy j)) B at hB
      simpa only [map_intCast] using hB
    exact MultivariateComparison.comparison_of_normal_bases
      (fun i r => (a i r : ℂ)) Q hy A B hc hA hB'
      f hQ rho hrho cost hcost epsilon N hepsilon hN hdegree
      (hn A.card hc hdim) hvanish
  · have hAz : A.card = 0 := Nat.eq_zero_of_not_pos hc
    have hcard : A.card = B.card := hA.card_eq.trans hB.card_eq.symm
    have hBz : B.card = 0 := hcard.symm.trans hAz
    have hAe : A = ∅ := Finset.card_eq_zero.mp hAz
    have hBe : B = ∅ := Finset.card_eq_zero.mp hBz
    simp [hAe, hBe]

/-- Weighted degree and vanishing at a minimal prime, together with directed
weight separation, force the selected monomials and additive coordinates to
be constant on that prime component. No basis-comparison hypothesis remains. -/
theorem constancy_of_weighted_vanishing [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (a : Fin m → Fin k → ℤ)
    (Q : Ideal (Polynomial ℂ k m)) [Q.IsPrime]
    (hy : ∀ r, primeResidueMap Q (MvPolynomial.X (Sum.inl r)) ≠ 0)
    {J : Type*} (f : J → Polynomial ℂ k m)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : (Fin k ⊕ Fin m) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : (Fin k ⊕ Fin m) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ q : ℕ, 0 < q → q ≤ k + m →
      ∀ B : Fin q → Fin k ⊕ Fin m, ∀ i,
        2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ word : List (Fin k ⊕ Fin m),
      wordCost cost word ≤ epsilon * N → frameWord (fun i r => (a i r : ℂ)) word p ∈ Q)
    (hseparated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
      (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
        (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
      ((A.card : ℝ) ^ A.card / epsilon ^ A.card) * (∏ j ∈ B, cost j) <
        ∏ j ∈ A, (rho j : ℝ)) :
    ∃ I : Finset (Fin k ⊕ Fin m),
      IsGreedyBasis (K := Q.ResidueField) (coordinateNormalFamily (primeResidueMap Q) Q)
        (Finset.univ.image Sum.inr) I ∧
      (∀ B, IsNormalBasis (K := Q.ResidueField)
        (frameNormalFamily (primeResidueMap Q) Q a hy) B →
          B ∩ Finset.univ.image Sum.inr = I) ∧
      ∀ i : Fin m, Sum.inr i ∈ I →
        (∃ c : ℂ, algebraMap ℂ Q.ResidueField c =
          ∏ r, primeResidueMap Q (MvPolynomial.X (Sum.inl r)) ^ a i r) ∧
        ∃ b : ℂ, MvPolynomial.X (Sum.inr i) - MvPolynomial.C b ∈ Q := by
  let : Algebra.EssFiniteType ℂ Q.ResidueField :=
    Algebra.EssFiniteType.comp ℂ (Polynomial ℂ k m) Q.ResidueField
  have hker (p : Polynomial ℂ k m) : primeResidueMap Q p = 0 ↔ p ∈ Q :=
    Ideal.algebraMap_residueField_eq_zero
  exact weighted_polynomial_constancy (primeResidueMap Q) Q hker a hy
    (fun j => (rho j : ℝ)) cost (fun c => (c : ℝ) ^ c / epsilon ^ c)
    (universal_comparison_of_weighted_vanishing a Q hy f hQ rho hrho cost hcost
      epsilon N hepsilon hN hdegree hn hvanish) hseparated

end
end GeneralizedLogarithms.GeometricConstancy

/-- info: 'GeneralizedLogarithms.GeometricConstancy.universal_comparison_of_weighted_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GeometricConstancy.universal_comparison_of_weighted_vanishing

/-- info: 'GeneralizedLogarithms.GeometricConstancy.constancy_of_weighted_vanishing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.GeometricConstancy.constancy_of_weighted_vanishing
