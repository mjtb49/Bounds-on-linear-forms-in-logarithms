import GeneralizedLogarithms.MultivariateJetVanishing
import GeneralizedLogarithms.MultivariateCurveConstancy
import GeneralizedLogarithms.MultifibreInequality

/-!
# The multivariate curve inequality from an auxiliary polynomial

High formal jets of one nonzero polynomial imply derivative vanishing under
excess contact. Persistence, weighted comparison and integer general position
then make every longitudinal coordinate constant. The actual multilogarithmic
contact bound on that fibre contradicts excess.

The theorem retains the auxiliary polynomial and numerical weight conditions
as inputs. It assumes neither derivative vanishing, a local order bound, nor
coordinate constancy. Its kernel-height input is independently discharged by
`MultivariateCurveConstancy.coordinateKernel_height_eq` for a coordinate-generated
field of transcendence degree one.
-/

namespace GeneralizedLogarithms.MultivariateCurveInequality

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing
open MultivariatePolynomialFrame MultivariateMultiplicity MultivariateFormalJet

variable {E J : Type*} [Field E] [Algebra ℂ E] {k m : ℕ}

/-- The curve inequality for actual multilogarithmic contacts, conditional only
on an auxiliary polynomial, its high jets, and the stated numerical geometry. -/
theorem weighted_curve_inequality_of_auxiliary_polynomial
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : Fin m → Fin k → ℤ) (hrows : ∀ i, a i ≠ 0)
    (hgeneral : IntegerGeneralPosition a) (z : Fin k ⊕ Fin m → E)
    (c : J → Fin k ⊕ Fin m → ℂ) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (hcenters : Function.Injective (fun j => fun r : Fin k => c j (Sum.inl r)))
    (hz : ∃ j, Transcendental ℂ (z j))
    (w v : Fin k ⊕ Fin m → ℚ) (hw : ∀ j, 0 < w j) (hv : ∀ j, 0 < v j)
    (t : Fin k ⊕ Fin m → ℝ) (ht : ∀ j, 0 < t j)
    (θ w₀ v₀ : ℝ) (hθ : 0 ≤ θ) (hv₀ : 0 < v₀)
    (hW : ∀ j, (w j : ℝ) =
      blockWeight (Finset.univ.image Sum.inr) (fun i => θ * t i) w₀ j)
    (hV : ∀ j, (v j : ℝ) = blockWeight (Finset.univ.image Sum.inr) t v₀ j)
    (σ : ℚ) (hσ : 0 < σ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (N : ℕ) (hN : 0 < N) (F : Polynomial ℂ k m) (hF : F ≠ 0)
    (hdegree : WeightedSliceDegree.SupportBound (fun j => (w j : ℝ)) (N : ℝ) F)
    (hjet : ∀ j, formalJet a (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1 + 3 * σ) * N))
    (h : ℕ) (hheight : (MultivariateCurveConstancy.coordinateKernel z).height ≤ h)
    (hbudget : ((h : ℝ) + 2) * epsilon ≤ (σ : ℝ))
    (hn : ∀ q : ℕ, 0 < q → q ≤ k + m →
      ∀ B : Fin q → Fin k ⊕ Fin m, ∀ i,
        2 ≤ rectangularCutoff (fun j => (v (B j) : ℝ)) (epsilon * N) i)
    (hseparated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
      (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
        (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
      ((A.card : ℝ) ^ A.card / epsilon ^ A.card) * (∏ j ∈ B, (v j : ℝ)) <
        ∏ j ∈ A, (w j : ℝ))
    (hgap : ∀ r d : ℕ, r < k → 1 ≤ d - r → d - r ≤ k → d ≤ 2 * k - 1 →
      (d : ℝ) ^ d / epsilon ^ d < θ ^ r * (w₀ / v₀) ^ (d - r))
    (hdiscount : (1 + (σ : ℝ)) * θ ≤ 1)
    (S : Finset (NormalizedPlace ℂ E)) (index : ∀ p, p ∈ S → J)
    (hc : ∀ p (hp : p ∈ S), Centered z (c (index p hp)) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))) :
    (1 + (σ : ℝ)) * ∑ p ∈ S,
      (MultifibreInequality.contact a z c hcY hz v S index hc hres p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  classical
  by_contra hnot
  have hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1 + (σ : ℝ)) * ∑ p ∈ S,
        (MultifibreInequality.contact a z c hcY hz v S index hc hres p : ℝ) :=
    lt_of_not_ge hnot
  have hS : S.Nonempty := by
    by_contra hs
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hsum : (∑ p ∈ S,
        (MultifibreInequality.contact a z c hcY hz v S index hc hres p : ℝ)) = 0 :=
      Finset.sum_eq_zero (by
        intro p hp
        exact False.elim (by simpa [he] using hp))
    rw [hsum, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z w)) hexcess
  obtain ⟨p₀, hp₀⟩ := hS
  have hY := MultivariateCurveConstancy.longitudinal_ne_zero_of_centered z
    (c (index p₀ hp₀)) p₀ (hc p₀ hp₀) (hcY (index p₀ hp₀))
  have hwords := MultivariateJetVanishing.frame_words_vanish_of_jets_and_excess_contact
    hfinite a z c hcY hz w v hw hv σ hσ N hN F hdegree hjet S index hc hres hexcess
  have htotal : ((h : ℝ) + 2) * (epsilon * (N : ℝ)) ≤ (σ : ℝ) * N := by
    calc
      _ = (((h : ℝ) + 2) * epsilon) * N := by ring
      _ ≤ (σ : ℝ) * N := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg N)
  have hconstant := MultivariateCurveConstancy.longitudinal_constants_of_vanishing z
    a hrows hgeneral w hw (fun j => (v j : ℝ)) (fun j => by exact_mod_cast hv j)
    t ht θ w₀ v₀ hv₀ hW hV epsilon (N : ℝ) hepsilon (by exact_mod_cast hN)
    F hF hdegree h hheight hY
    (fun word hword => hwords word (hword.trans htotal)) hn hseparated hgap
  choose b hb using hconstant
  let x : Fin m → E := fun i => z (Sum.inr i)
  have hzeq : z = MultifibreContact.fibre b x := by
    funext j
    cases j with
    | inl r => exact hb r
    | inr i => rfl
  have hzf : ∃ j, Transcendental ℂ (MultifibreContact.fibre b x j) := by
    simpa only [← hzeq] using hz
  have hcf : ∀ p (hp : p ∈ S),
      Centered (MultifibreContact.fibre b x) (c (index p hp)) p := by
    simpa only [← hzeq] using hc
  have hratio : ∀ i, (w (Sum.inr i) : ℝ) = θ * (v (Sum.inr i) : ℝ) := by
    intro i
    have hw' : (w (Sum.inr i) : ℝ) = θ * t (Sum.inr i) := by
      simpa [blockWeight] using hW (Sum.inr i)
    have hv' : (v (Sum.inr i) : ℝ) = t (Sum.inr i) := by
      simpa [blockWeight] using hV (Sum.inr i)
    rw [hw', hv']
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hno := MultifibreInequality.multifibre_no_excess hfinite a b x c hcY hcenters hzf
    w v (fun i => hw (Sum.inr i)) (fun i => hv (Sum.inr i)) θ hθ hratio
    S index hcf hres (σ : ℝ) (by linarith) hdiscount
  have hno' : ¬ CurveContactSum.weightedDegree hfinite z w <
      (1 + (σ : ℝ)) * ∑ p ∈ S,
        (MultifibreInequality.contact a z c hcY hz v S index hc hres p : ℝ) := by
    simpa only [← hzeq] using hno
  exact hno' hexcess

end
end GeneralizedLogarithms.MultivariateCurveInequality

/-- info: 'GeneralizedLogarithms.MultivariateCurveInequality.weighted_curve_inequality_of_auxiliary_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveInequality.weighted_curve_inequality_of_auxiliary_polynomial
