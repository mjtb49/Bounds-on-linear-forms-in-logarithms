import GeneralizedLogarithms.PersistentConstancy
import GeneralizedLogarithms.SmallRankExclusion
import GeneralizedLogarithms.IntegerGeneralPosition

/-!
# Longitudinal constancy from one polynomial

This composes the persistent-prime construction, weighted local multiplicity
comparison, small-rank exclusion, and integer general position. It constructs
a component on which every longitudinal coordinate is constant. Those equations
also hold in the initial prime containing the component ideal.

The initial prime height and derivative-word vanishing still have to come from
curve contact. The numerical separation and longitudinal gap are explicit
hypotheses. This file does not assert the final interpolation theorem.
-/

namespace GeneralizedLogarithms.PersistentLongitudinal

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponentApprox
open NormalBasisRigidity
open MultivariatePolynomialFrame MultivariateMultiplicity MultivariatePersistence
open PolynomialPrimeAdapter

variable {k m : ℕ}

/-- Under the numerical weight conditions, bounded derivative vanishing of one
nonzero polynomial forces every longitudinal coordinate to be constant, first
on a constructed persistent component and then on the initial prime. -/
theorem exists_persistent_longitudinal_equations
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (a : Fin m → Fin k → ℤ) (hrows : ∀ i, a i ≠ 0)
    (hgeneral : IntegerGeneralPosition a)
    (rho : (Fin k ⊕ Fin m) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : (Fin k ⊕ Fin m) → ℝ) (hcost : ∀ i, 0 < cost i)
    (t : (Fin k ⊕ Fin m) → ℝ) (ht : ∀ i, 0 < t i)
    (θ w₀ v₀ : ℝ) (hv₀ : 0 < v₀)
    (hW : ∀ i, (rho i : ℝ) =
      blockWeight (Finset.univ.image Sum.inr) (fun j => θ * t j) w₀ i)
    (hV : ∀ i, cost i = blockWeight (Finset.univ.image Sum.inr) t v₀ i)
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
        ∏ j ∈ A, (rho j : ℝ))
    (hgap : ∀ r c : ℕ, r < k → 1 ≤ c - r → c - r ≤ k → c ≤ 2 * k - 1 →
      (c : ℝ) ^ c / epsilon ^ c < θ ^ r * (w₀ / v₀) ^ (c - r)) :
    ∃ r < h + 2, ∃ (Q : Ideal (Polynomial ℂ k m)) (hQ : Q.IsPrime),
      Q ≠ ⊥ ∧ Q ≤ P ∧ 1 ≤ Q.height ∧ Q.height ≤ h ∧
      Q ∈ (derivativeIdeal (fun i r => (a i r : ℂ)) cost
        ((r : ℝ) * (epsilon * N)) F).minimalPrimes ∧
      ∀ s : Fin k, ∃ c : ℂ,
        MvPolynomial.X (Sum.inl s) - MvPolynomial.C c ∈ Q ∧
        MvPolynomial.X (Sum.inl s) - MvPolynomial.C c ∈ P := by
  let ac : Fin m → Fin k → ℂ := fun i r => (a i r : ℂ)
  obtain ⟨r, hr, Q, hQ, hQne, hQr, _, hQP, hQlo, hQhi, hwords⟩ :=
    exists_persistent_prime ac cost (fun i => (hcost i).le)
      (epsilon * N) (mul_pos hepsilon hN).le F hF h P hP hheight hvanish
  let := hQ
  let : CharZero Q.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap ℂ Q.ResidueField).injective
  let : Algebra.EssFiniteType ℂ Q.ResidueField :=
    Algebra.EssFiniteType.comp ℂ (Polynomial ℂ k m) Q.ResidueField
  have hy : ∀ s : Fin k, primeResidueMap Q (MvPolynomial.X (Sum.inl s)) ≠ 0 := by
    intro s hs
    exact hY s (hQP (Ideal.algebraMap_residueField_eq_zero.mp hs))
  have hker (p : Polynomial ℂ k m) : primeResidueMap Q p = 0 ↔ p ∈ Q :=
    Ideal.algebraMap_residueField_eq_zero
  have hrhoR : ∀ j, (0 : ℝ) ≤ (rho j : ℝ) := by
    intro j
    exact_mod_cast (hrho j).le
  let bound : ℝ := (r : ℝ) * (epsilon * N)
  have hQeq : Q ∈ (Ideal.span (Set.range (equations ac cost bound F))).minimalPrimes := by
    rwa [span_equations]
  have hcomparison := GeometricConstancy.universal_comparison_of_weighted_vanishing
    a Q hy (equations ac cost bound F) hQeq rho hrho cost hcost epsilon N hepsilon hN
    (fun word => MultivariateDegree.equation_weighted_sum_le ac cost
      (fun j => (rho j : ℝ)) bound N F hdegree hrhoR word) hn
    (by simpa only [span_equations] using hwords)
  have hconst := SmallRankExclusion.longitudinal_equations_of_weighted_comparison
    (primeResidueMap Q) Q hker hQne a hrows hy t ht θ w₀ v₀ hv₀
    (fun c => (c : ℝ) ^ c / epsilon ^ c)
    (by simpa only [← hW, ← hV] using hcomparison)
    (by simpa only [← hW, ← hV] using hseparated) hgap
    (IntegerGeneralPosition.selected_rows_span Q.ResidueField a hgeneral)
  refine ⟨r, hr, Q, hQ, hQne, hQP, hQlo, hQhi, hQr, ?_⟩
  intro s
  obtain ⟨c, hc⟩ := hconst s
  exact ⟨c, hc, hQP hc⟩

end
end GeneralizedLogarithms.PersistentLongitudinal

/-- info: 'GeneralizedLogarithms.PersistentLongitudinal.exists_persistent_longitudinal_equations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.PersistentLongitudinal.exists_persistent_longitudinal_equations
