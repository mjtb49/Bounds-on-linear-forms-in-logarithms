import GeneralizedLogarithms.GeometricConstancy
import GeneralizedLogarithms.MultivariateDegree

/-!
# Constancy on a constructed persistent component

Starting with a nonzero polynomial and bounded-word vanishing in a prime
of bounded height, construct a persistent nonzero prime, supply its weighted
equations and all-ideal-elements vanishing, and apply geometric constancy.
The remaining geometric input is the original prime's height and word
vanishing, together with numerical weight separation and cutoff bounds.
-/

namespace GeneralizedLogarithms.PersistentConstancy

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponentApprox
open NormalBasisRigidity
open MultivariatePolynomialFrame MultivariateMultiplicity MultivariatePersistence
open PolynomialPrimeAdapter

variable {k m : ℕ}

/-- The full normal-basis and function-field constancy conclusion on a prime.
The residue-field nonvanishing witnesses are included, not assumed externally. -/
def PrimeConstancyConclusion [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (a : Fin m → Fin k → ℤ) (Q : Ideal (Polynomial ℂ k m)) [Q.IsPrime] : Prop :=
  ∃ hy : ∀ r : Fin k, primeResidueMap Q (MvPolynomial.X (Sum.inl r)) ≠ 0,
    ∃ I : Finset (Fin k ⊕ Fin m),
      IsGreedyBasis (K := Q.ResidueField) (coordinateNormalFamily (primeResidueMap Q) Q)
        (Finset.univ.image Sum.inr) I ∧
      (∀ B, IsNormalBasis (K := Q.ResidueField)
        (frameNormalFamily (primeResidueMap Q) Q a hy) B →
          B ∩ Finset.univ.image Sum.inr = I) ∧
      ∀ i : Fin m, Sum.inr i ∈ I →
        (∃ c : ℂ, algebraMap ℂ Q.ResidueField c =
          ∏ r, primeResidueMap Q (MvPolynomial.X (Sum.inl r)) ^ a i r) ∧
        ∃ b : ℂ, MvPolynomial.X (Sum.inr i) - MvPolynomial.C b ∈ Q

/-- The persistent component and its local multiplicity comparison are both
constructed. Ambient curve containment and numerical separation remain inputs. -/
theorem exists_persistent_constancy [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (a : Fin m → Fin k → ℤ)
    (rho : (Fin k ⊕ Fin m) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : (Fin k ⊕ Fin m) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (F : Polynomial ℂ k m) (hF : F ≠ 0)
    (hdegree : WeightedSliceDegree.SupportBound (fun j => (rho j : ℝ)) N F)
    (h : ℕ) (P : Ideal (Polynomial ℂ k m)) (hP : P.IsPrime)
    (hheight : P.height ≤ h)
    (hY : ∀ r : Fin k, MvPolynomial.X (Sum.inl r) ∉ P)
    (hvanish : ∀ word : List (Fin k ⊕ Fin m),
      wordCost cost word ≤ ((h : ℝ) + 2) * (epsilon * N) →
        frameWord (fun i r => (a i r : ℂ)) word F ∈ P)
    (hn : ∀ q : ℕ, 0 < q → q ≤ k + m →
      ∀ B : Fin q → Fin k ⊕ Fin m, ∀ i,
        2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hseparated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
      (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
        (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
      ((A.card : ℝ) ^ A.card / epsilon ^ A.card) * (∏ j ∈ B, cost j) <
        ∏ j ∈ A, (rho j : ℝ)) :
    ∃ r < h + 2, ∃ (Q : Ideal (Polynomial ℂ k m)) (hQ : Q.IsPrime),
      letI := hQ
      Q ≠ ⊥ ∧ Q ≤ P ∧ 1 ≤ Q.height ∧ Q.height ≤ h ∧
      Q ∈ (derivativeIdeal (fun i r => (a i r : ℂ)) cost
        ((r : ℝ) * (epsilon * N)) F).minimalPrimes ∧
      PrimeConstancyConclusion a Q := by
  let ac : Fin m → Fin k → ℂ := fun i r => (a i r : ℂ)
  obtain ⟨r, hr, Q, hQ, hQne, hQr, _, hQP, hQlo, hQhi, hwords⟩ :=
    exists_persistent_prime ac cost (fun i => (hcost i).le)
      (epsilon * N) (mul_pos hepsilon hN).le F hF h P hP hheight hvanish
  letI := hQ
  have hy : ∀ r : Fin k, primeResidueMap Q (MvPolynomial.X (Sum.inl r)) ≠ 0 := by
    intro j hj
    exact hY j (hQP (Ideal.algebraMap_residueField_eq_zero.mp hj))
  have hrhoR : ∀ j, (0 : ℝ) ≤ (rho j : ℝ) := by
    intro j
    exact_mod_cast (hrho j).le
  let bound : ℝ := (r : ℝ) * (epsilon * N)
  have hQeq : Q ∈ (Ideal.span (Set.range (equations ac cost bound F))).minimalPrimes := by
    rwa [span_equations]
  have hconst := GeometricConstancy.constancy_of_weighted_vanishing a Q hy
    (equations ac cost bound F) hQeq rho hrho cost hcost epsilon N hepsilon hN
    (fun word => MultivariateDegree.equation_weighted_sum_le ac cost
      (fun j => (rho j : ℝ)) bound N F hdegree hrhoR word) hn
    (by simpa only [span_equations] using hwords) hseparated
  exact ⟨r, hr, Q, hQ, hQne, hQP, hQlo, hQhi, hQr, hy, hconst⟩

end
end GeneralizedLogarithms.PersistentConstancy

/-- info: 'GeneralizedLogarithms.PersistentConstancy.exists_persistent_constancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.PersistentConstancy.exists_persistent_constancy
