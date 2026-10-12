import GeneralizedLogarithms.MultifibreContact
import GeneralizedLogarithms.MultilogBranchCoordinates

/-!
# The theta discount for actual multilogarithmic place contacts

This composes the DVR branch-coordinate reduction with the constant-fibre
contact bound. The contacts in the conclusions are defined using actual DVR
expansions; no contact-to-ordinary identity is assumed by these theorems.

The longitudinal coordinates are assumed constant. Obtaining that hypothesis
from excess contact still requires the multivariate auxiliary-jet and
derivative-order argument.
-/

namespace GeneralizedLogarithms.MultifibreInequality

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open CurveValuationCenter CurveCenters PlaceValuationRing

variable {E J : Type*} [Field E] [Algebra ℂ E] {k m : ℕ}

/-- The actual multilogarithmic place contact on a selected finite family of
centered places, extended by zero outside that family. -/
def contact (a : Fin m → Fin k → ℤ) (z : Fin k ⊕ Fin m → E)
    (c : J → Fin k ⊕ Fin m → ℂ) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (hz : ∃ j, Transcendental ℂ (z j)) (v : Fin k ⊕ Fin m → ℚ)
    (S : Finset (NormalizedPlace ℂ E)) (index : ∀ p, p ∈ S → J)
    (hc : ∀ p (hp : p ∈ S), Centered z (c (index p hp)) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (p : NormalizedPlace ℂ E) : ℚ := by
  classical
  exact if hp : p ∈ S then
    letI := hres p hp
    MultilogBranchCoordinates.placeContact p a z (c (index p hp)) (hcY (index p hp))
      (hc p hp) (Centered.exists_nonzero_difference z (c (index p hp)) hz) v
  else 0

theorem contact_eq (a : Fin m → Fin k → ℤ) (z : Fin k ⊕ Fin m → E)
    (c : J → Fin k ⊕ Fin m → ℂ) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (hz : ∃ j, Transcendental ℂ (z j)) (v : Fin k ⊕ Fin m → ℚ)
    (S : Finset (NormalizedPlace ℂ E)) (index : ∀ p, p ∈ S → J)
    (hc : ∀ p (hp : p ∈ S), Centered z (c (index p hp)) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (p : NormalizedPlace ℂ E) (hp : p ∈ S) :
    contact a z c hcY hz v S index hc hres p =
      letI := hres p hp
      MultilogBranchCoordinates.placeContact p a z (c (index p hp)) (hcY (index p hp))
        (hc p hp) (Centered.exists_nonzero_difference z (c (index p hp)) hz) v := by
  simp only [contact, dif_pos hp]

/-- The theta discount for the genuine multilogarithmic contacts of a fibre.
Only injectivity of the complete longitudinal center tuple is required. -/
theorem multifibre_contact_sum_le
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : Fin m → Fin k → ℤ) (b : Fin k → ℂ) (x : Fin m → E)
    (c : J → Fin k ⊕ Fin m → ℂ) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (hcenters : Function.Injective (fun j => fun r : Fin k => c j (Sum.inl r)))
    (hz : ∃ j, Transcendental ℂ (MultifibreContact.fibre b x j))
    (w v : Fin k ⊕ Fin m → ℚ)
    (hw : ∀ i, 0 < w (Sum.inr i)) (hv : ∀ i, 0 < v (Sum.inr i))
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hratio : ∀ i, (w (Sum.inr i) : ℝ) = θ * (v (Sum.inr i) : ℝ))
    (S : Finset (NormalizedPlace ℂ E)) (index : ∀ p, p ∈ S → J)
    (hc : ∀ p (hp : p ∈ S), Centered (MultifibreContact.fibre b x) (c (index p hp)) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))) :
    ∑ p ∈ S, (contact a (MultifibreContact.fibre b x) c hcY hz v S index hc hres p : ℝ) ≤
      θ * CurveContactSum.weightedDegree hfinite (MultifibreContact.fibre b x) w := by
  apply MultifibreContact.multifibre_contact_sum_le hfinite b x c hcenters hz
    w v hw hv θ hθ hratio S index hc hres
  intro p hp
  let := hres p hp
  apply congrArg (fun q : ℚ => (q : ℝ))
  rw [contact_eq a (MultifibreContact.fibre b x) c hcY hz v S index hc hres p hp]
  have hY : ∀ r, MultifibreContact.fibre b x (Sum.inl r) =
      algebraMap ℂ E (c (index p hp) (Sum.inl r)) := by
    intro r
    rw [MultifibreContact.fibre_inl,
      (hc p hp).constant_coordinate (Sum.inl r) (b r) rfl]
  simpa only [MultifibreContact.fibre_inr] using
    MultilogBranchCoordinates.placeContact_of_constant_longitudinal p a
      (MultifibreContact.fibre b x) (c (index p hp)) (hcY (index p hp)) (hc p hp)
      (Centered.exists_nonzero_difference (MultifibreContact.fibre b x) (c (index p hp)) hz)
      v hY

/-- An amplified contact factor at most one excludes excess on the constant
longitudinal fibre, for actual multilogarithmic place contacts. -/
theorem multifibre_no_excess
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : Fin m → Fin k → ℤ) (b : Fin k → ℂ) (x : Fin m → E)
    (c : J → Fin k ⊕ Fin m → ℂ) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (hcenters : Function.Injective (fun j => fun r : Fin k => c j (Sum.inl r)))
    (hz : ∃ j, Transcendental ℂ (MultifibreContact.fibre b x j))
    (w v : Fin k ⊕ Fin m → ℚ)
    (hw : ∀ i, 0 < w (Sum.inr i)) (hv : ∀ i, 0 < v (Sum.inr i))
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hratio : ∀ i, (w (Sum.inr i) : ℝ) = θ * (v (Sum.inr i) : ℝ))
    (S : Finset (NormalizedPlace ℂ E)) (index : ∀ p, p ∈ S → J)
    (hc : ∀ p (hp : p ∈ S), Centered (MultifibreContact.fibre b x) (c (index p hp)) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (σ : ℝ) (hσ : 0 ≤ 1 + σ) (hdiscount : (1 + σ) * θ ≤ 1) :
    ¬ CurveContactSum.weightedDegree hfinite (MultifibreContact.fibre b x) w <
      (1 + σ) * ∑ p ∈ S,
        (contact a (MultifibreContact.fibre b x) c hcY hz v S index hc hres p : ℝ) := by
  exact MultifibreContact.no_excess_of_contact_discount S
    (fun p => (contact a (MultifibreContact.fibre b x) c hcY hz v S index hc hres p : ℝ))
    (CurveContactSum.weightedDegree hfinite (MultifibreContact.fibre b x) w) θ σ
    (CurveContactSum.weightedDegree_nonneg hfinite (MultifibreContact.fibre b x) w)
    hσ hdiscount
    (multifibre_contact_sum_le hfinite a b x c hcY hcenters hz w v hw hv θ hθ hratio
      S index hc hres)

end
end GeneralizedLogarithms.MultifibreInequality

/-- info: 'GeneralizedLogarithms.MultifibreInequality.multifibre_contact_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultifibreInequality.multifibre_contact_sum_le

/-- info: 'GeneralizedLogarithms.MultifibreInequality.multifibre_no_excess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultifibreInequality.multifibre_no_excess
