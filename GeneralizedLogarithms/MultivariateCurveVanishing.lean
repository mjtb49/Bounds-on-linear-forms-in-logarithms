import GeneralizedLogarithms.MultivariateDegree
import LogIrrationalityMeasure.Geometry.CurveContactSum

/-!
# Excess contact forces bounded frame derivatives to vanish on a curve

The local order estimate remains an explicit hypothesis: it is the estimate
that a multivariate jet adapter must supply. This module combines that estimate
with preservation of weighted polynomial degree and the existing curve product
formula. It does not assert that arbitrary contacts satisfy the local estimate,
and it does not assert a height bound for the curve's evaluation kernel.
-/

namespace GeneralizedLogarithms
namespace MultivariateCurveVanishing

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open CurveValuationCenter
open MultivariatePolynomialFrame MultivariateMultiplicity MultivariatePersistence

variable {E : Type*} [Field E] [Algebra ℂ E] {k m : ℕ}

/-- Excess contact forces all frame words within cost `σ*N` to vanish.
The initial local order budget is `(1+3*σ)*N`; after these derivatives at least
`(1+2*σ)*N` remains. The order estimate for a nonzero evaluation is an explicit
input, to be obtained separately from local jets. -/
theorem frame_words_vanish_of_excess_contact
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : (Fin k ⊕ Fin m) → E)
    (a : Fin m → Fin k → ℂ)
    (w : (Fin k ⊕ Fin m) → ℚ) (hw : ∀ i, 0 < w i)
    (cost : (Fin k ⊕ Fin m) → ℝ)
    (σ N : ℝ) (hσ : 0 < σ) (hN : 0 < N)
    (F : Polynomial ℂ k m)
    (hF : WeightedSliceDegree.SupportBound (fun i => (w i : ℝ)) N F)
    (S : Finset (NormalizedPlace ℂ E)) (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p ∈ S, 0 ≤ μ p)
    (hlocal : ∀ word : List (Fin k ⊕ Fin m),
      MvPolynomial.aeval z (frameWord a word F) ≠ 0 → ∀ p ∈ S,
        μ p * ((1 + 3 * σ) * N - wordCost cost word) ≤
          (WeightedPolynomialPole.coordinateOrder p.valuation
            (MvPolynomial.aeval z (frameWord a word F)) : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1 + σ) * ∑ p ∈ S, μ p) :
    ∀ word : List (Fin k ⊕ Fin m), wordCost cost word ≤ σ * N →
      MvPolynomial.aeval z (frameWord a word F) = 0 := by
  intro word hword
  have hwR : ∀ i, (0 : ℝ) ≤ (w i : ℝ) := by
    intro i
    exact_mod_cast (hw i).le
  have hdegree : ∀ d ∈ (frameWord a word F).support,
      Finsupp.weight (fun i => (w i : ℝ)) d ≤ N :=
    MultivariateDegree.supportBound_frameWord a (fun i => (w i : ℝ)) N F hF hwR word
  have hsum : 0 ≤ ∑ p ∈ S, μ p := Finset.sum_nonneg hμ
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite z w hw
    N ((1 + 2 * σ) * N) hN.le (frameWord a word F) hdegree S μ
  · intro hne p hp
    have hret : (1 + 2 * σ) * N ≤ (1 + 3 * σ) * N - wordCost cost word := by
      nlinarith
    have h := (mul_le_mul_of_nonneg_left hret (hμ p hp)).trans (hlocal word hne p hp)
    simpa only [mul_comm] using h
  · calc
      N * CurveContactSum.weightedDegree hfinite z w < N * ((1 + σ) * ∑ p ∈ S, μ p) :=
        mul_lt_mul_of_pos_left hexcess hN
      _ = (1 + σ) * (N * ∑ p ∈ S, μ p) := by ring
      _ ≤ (1 + 2 * σ) * (N * ∑ p ∈ S, μ p) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hN.le hsum)
      _ = ((1 + 2 * σ) * N) * ∑ p ∈ S, μ p := by ring

/-- Evaluation vanishing of bounded frame words is exactly the containment
needed to begin the persistent-ideal construction. This lemma does not claim
that the evaluation kernel has any particular height. -/
theorem derivativeIdeal_le_evaluationKernel_of_words_vanish
    (z : (Fin k ⊕ Fin m) → E) (a : Fin m → Fin k → ℂ)
    (cost : (Fin k ⊕ Fin m) → ℝ) (bound : ℝ) (F : Polynomial ℂ k m)
    (hvanish : ∀ word : List (Fin k ⊕ Fin m), wordCost cost word ≤ bound →
      MvPolynomial.aeval z (frameWord a word F) = 0) :
    derivativeIdeal a cost bound F ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
  apply (derivativeIdeal_le_iff a cost bound F _).mpr
  intro word hw
  exact hvanish word hw

end
end MultivariateCurveVanishing
end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.MultivariateCurveVanishing.frame_words_vanish_of_excess_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveVanishing.frame_words_vanish_of_excess_contact

/-- info: 'GeneralizedLogarithms.MultivariateCurveVanishing.derivativeIdeal_le_evaluationKernel_of_words_vanish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveVanishing.derivativeIdeal_le_evaluationKernel_of_words_vanish
