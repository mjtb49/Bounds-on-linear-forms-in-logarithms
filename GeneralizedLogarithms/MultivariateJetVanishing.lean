import GeneralizedLogarithms.MultivariateCurveVanishing
import GeneralizedLogarithms.MultivariateBranchEvaluation
import GeneralizedLogarithms.MultifibreInequality

/-!
# Actual multilogarithmic jets imply derivative vanishing under excess contact

The contact function is defined by the actual DVR branch expansions at the
selected centered places. The local order estimate and nonnegativity required
by `MultivariateCurveVanishing` are discharged here from those branches and
the formal-jet hypotheses.
-/

namespace GeneralizedLogarithms.MultivariateJetVanishing

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open CurveValuationCenter CurveCenters PlaceValuationRing
open MultivariatePolynomialFrame MultivariateMultiplicity MultivariateFormalJet

theorem cast_word_cost {ι : Type*} (v : ι → ℚ) (word : List ι) :
    (((word.map v).sum : ℚ) : ℝ) = wordCost (fun i => (v i : ℝ)) word := by
  induction word with
  | nil => simp [wordCost]
  | cons i word ih => simp [wordCost] at ih ⊢; exact ih

variable {E J : Type*} [Field E] [Algebra ℂ E] {k m : ℕ}

/-- Excess genuine multilogarithmic contact forces every frame word within
cost `σ*N` to vanish after evaluation on the curve. The local order inequality
is proved from the supplied formal jets, rather than assumed. -/
theorem frame_words_vanish_of_jets_and_excess_contact
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : Fin m → Fin k → ℤ) (z : (Fin k ⊕ Fin m) → E)
    (c : J → (Fin k ⊕ Fin m) → ℂ) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (hz : ∃ j, Transcendental ℂ (z j))
    (w v : (Fin k ⊕ Fin m) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (σ : ℚ) (hσ : 0 < σ) (N : ℕ) (hN : 0 < N)
    (F : Polynomial ℂ k m)
    (hF : WeightedSliceDegree.SupportBound (fun i => (w i : ℝ)) (N : ℝ) F)
    (hjet : ∀ j, formalJet a (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1 + 3 * σ) * N))
    (S : Finset (NormalizedPlace ℂ E)) (index : ∀ p, p ∈ S → J)
    (hc : ∀ p (hp : p ∈ S), Centered z (c (index p hp)) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1 + (σ : ℝ)) * ∑ p ∈ S,
        (MultifibreInequality.contact a z c hcY hz v S index hc hres p : ℝ)) :
    ∀ word : List (Fin k ⊕ Fin m),
      wordCost (fun i => (v i : ℝ)) word ≤ (σ : ℝ) * N →
        MvPolynomial.aeval z (frameWord (fun i r => (a i r : ℂ)) word F) = 0 := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply MultivariateCurveVanishing.frame_words_vanish_of_excess_contact
    hfinite z (fun i r => (a i r : ℂ)) w hw (fun i => (v i : ℝ))
    (σ : ℝ) (N : ℝ) hσR hNR F hF S
    (fun p => (MultifibreInequality.contact a z c hcY hz v S index hc hres p : ℝ))
  · intro p hp
    letI := hres p hp
    have hnonneg : 0 ≤ MultifibreInequality.contact a z c hcY hz v S index hc hres p := by
      rw [MultifibreInequality.contact_eq a z c hcY hz v S index hc hres p hp]
      exact (MultilogBranchCoordinates.placeContact_pos p a z (c (index p hp))
        (hcY (index p hp)) (hc p hp)
        (Centered.exists_nonzero_difference z (c (index p hp)) hz) v hv).le
    exact_mod_cast hnonneg
  · intro word hne p hp
    letI := hres p hp
    rw [MultifibreInequality.contact_eq a z c hcY hz v S index hc hres p hp,
      ← cast_word_cost v word]
    exact_mod_cast (MultivariateBranchEvaluation.frameWord_field_order_lower p a z
      (c (index p hp)) (hcY (index p hp)) (hc p hp)
      (Centered.exists_nonzero_difference z (c (index p hp)) hz)
      v hv ((1 + 3 * σ) * N) F (hjet (index p hp)) word hne)
  · exact hexcess

end
end GeneralizedLogarithms.MultivariateJetVanishing

/-- info: 'GeneralizedLogarithms.MultivariateJetVanishing.frame_words_vanish_of_jets_and_excess_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateJetVanishing.frame_words_vanish_of_jets_and_excess_contact
