import GeneralizedLogarithms.MultivariateAuxiliaryPolynomial
import GeneralizedLogarithms.MultivariateCurveInequality
import LogIrrationalityMeasure.Geometry.PlaceLocalRing

/-!
# The multivariate curve inequality from volume and numerical weights

The strict volume inequality supplies auxiliary polynomials for all sufficiently
large degrees. The same degree can be chosen positive and large enough for every
rectangular cutoff. The checked curve inequality can therefore be applied with
no auxiliary-polynomial, jet-vanishing, or cutoff-existence assumptions.

The intrinsic version uses all places centered at the finite center family and
derives the geometric field, residue and height inputs from a generated function
field of transcendence degree one. Weight separation, the longitudinal gap and
the volume inequality remain explicit numerical hypotheses.
-/

namespace GeneralizedLogarithms.MultivariateCurveInterpolation

noncomputable section

open scoped BigOperators
open Filter
open LogIrrationalityMeasure.LogExponent
open LogIrrationalityMeasure.LogExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing
open MultivariatePolynomialFrame MultivariateMultiplicity MultivariateFormalJet

variable {E J : Type*} [Field E] [Algebra ℂ E] [Fintype J] {k m : ℕ}

/-- Volume and the numerical weight conditions imply the actual contact
inequality. An auxiliary polynomial and all sufficiently large cutoffs are
constructed within the proof. -/
theorem weighted_curve_inequality
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
    (hvol : (Fintype.card J : ℝ) * (1 + 3 * (σ : ℝ)) ^ (k + m) *
      (∏ j, (w j : ℝ)) / (∏ j, (v j : ℝ)) < 1)
    (h : ℕ) (hheight : (MultivariateCurveConstancy.coordinateKernel z).height ≤ h)
    (hbudget : ((h : ℝ) + 2) * epsilon ≤ (σ : ℝ))
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
  have hscale : (0 : ℚ) < 1 + 3 * σ := by linarith
  have hvol' : (Fintype.card J : ℝ) * ((1 + 3 * σ : ℚ) : ℝ) ^ (k + m) *
      (∏ j, (w j : ℝ)) / (∏ j, (v j : ℝ)) < 1 := by
    simpa using hvol
  have haux := MultivariateAuxiliaryPolynomial.eventually_exists_formalJet_auxiliaryPolynomial_nat
    a w v hw hv (scale := 1 + 3 * σ) hscale hvol' c
  have hrect := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (MultivariateComparison.eventually_uniform_rectangularCutoff_two_le (k + m)
      (fun j : Fin k ⊕ Fin m => (v j : ℝ))
      (fun j => by exact_mod_cast hv j) epsilon hepsilon)
  have hpositive : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  obtain ⟨N, hN, hn, F, hF, hdegree, hjet⟩ := (hpositive.and (hrect.and haux)).exists
  exact MultivariateCurveInequality.weighted_curve_inequality_of_auxiliary_polynomial
    hfinite a hrows hgeneral z c hcY hcenters hz w v hw hv t ht θ w₀ v₀ hθ hv₀
    hW hV σ hσ epsilon hepsilon N hN F hF hdegree hjet h hheight hbudget hn
    hseparated hgap hdiscount S index hc hres

/-- Coordinate generation and transcendence degree one ensure that the curve
has a transcendental coordinate. -/
theorem nonconstant_coordinates (z : Fin k ⊕ Fin m → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ∃ j, Transcendental ℂ (z j) := by
  let : Algebra.Transcendental ℂ E :=
    trdeg_ne_zero_iff.mp (by rw [htrdeg]; exact one_ne_zero)
  exact CurveCenters.exists_transcendental_coordinate z hgen
    (Algebra.Transcendental.transcendental (R := ℂ) (A := E))

/-- Choose the center of a place from the complete finite set of centered places. -/
def centerIndex
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin k ⊕ Fin m → E) (c : J → Fin k ⊕ Fin m → ℂ)
    (hz : ∃ j, Transcendental ℂ (z j))
    (p : NormalizedPlace ℂ E) (hp : p ∈ centerPlaces z c hz hfinite) : J :=
  Classical.choose ((mem_centerPlaces z c hz hfinite p).mp hp)

theorem centerIndex_centered
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin k ⊕ Fin m → E) (c : J → Fin k ⊕ Fin m → ℂ)
    (hz : ∃ j, Transcendental ℂ (z j))
    (p : NormalizedPlace ℂ E) (hp : p ∈ centerPlaces z c hz hfinite) :
    Centered z (c (centerIndex hfinite z c hz p hp)) p :=
  Classical.choose_spec ((mem_centerPlaces z c hz hfinite p).mp hp)

/-- The full centered-place inequality for a coordinate-generated curve field.
Height, field finiteness, residue integrality, auxiliary polynomial existence,
cutoff size and coordinate nonconstancy are all discharged here. -/
theorem intrinsic_weighted_curve_inequality [Algebra.EssFiniteType ℂ E]
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (a : Fin m → Fin k → ℤ) (hrows : ∀ i, a i ≠ 0)
    (hgeneral : IntegerGeneralPosition a) (z : Fin k ⊕ Fin m → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (c : J → Fin k ⊕ Fin m → ℂ) (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (hcenters : Function.Injective (fun j => fun r : Fin k => c j (Sum.inl r)))
    (w v : Fin k ⊕ Fin m → ℚ) (hw : ∀ j, 0 < w j) (hv : ∀ j, 0 < v j)
    (t : Fin k ⊕ Fin m → ℝ) (ht : ∀ j, 0 < t j)
    (θ w₀ v₀ : ℝ) (hθ : 0 ≤ θ) (hv₀ : 0 < v₀)
    (hW : ∀ j, (w j : ℝ) =
      blockWeight (Finset.univ.image Sum.inr) (fun i => θ * t i) w₀ j)
    (hV : ∀ j, (v j : ℝ) = blockWeight (Finset.univ.image Sum.inr) t v₀ j)
    (σ : ℚ) (hσ : 0 < σ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hvol : (Fintype.card J : ℝ) * (1 + 3 * (σ : ℝ)) ^ (k + m) *
      (∏ j, (w j : ℝ)) / (∏ j, (v j : ℝ)) < 1)
    (hbudget : ((k + m : ℕ) + 1 : ℝ) * epsilon ≤ (σ : ℝ))
    (hseparated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
      ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
      (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
        (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
      ((A.card : ℝ) ^ A.card / epsilon ^ A.card) * (∏ j ∈ B, (v j : ℝ)) <
        ∏ j ∈ A, (w j : ℝ))
    (hgap : ∀ r d : ℕ, r < k → 1 ≤ d - r → d - r ≤ k → d ≤ 2 * k - 1 →
      (d : ℝ) ^ d / epsilon ^ d < θ ^ r * (w₀ / v₀) ^ (d - r))
    (hdiscount : (1 + (σ : ℝ)) * θ ≤ 1) :
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := nonconstant_coordinates z hgen htrdeg
    let S := centerPlaces z c hz hfinite
    let index := centerIndex hfinite z c hz
    let hc := centerIndex_centered hfinite z c hz
    let hres := fun p (_ : p ∈ S) => PlaceLocalRing.residue_integral htrdeg.le p
    (1 + (σ : ℝ)) * ∑ p ∈ S,
      (MultifibreInequality.contact a z c hcY hz v S index hc hres p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  dsimp only
  have hz := nonconstant_coordinates z hgen htrdeg
  have hdim : 0 < k + m := by
    obtain ⟨j, _⟩ := hz
    cases j with
    | inl r => have := r.isLt; omega
    | inr i => have := i.isLt; omega
  have hcast : (((k + m - 1 : ℕ) : ℝ) + 2) = ((k + m : ℕ) + 1 : ℝ) := by
    have hn : k + m - 1 + 2 = k + m + 1 := by omega
    exact_mod_cast hn
  have hbudget' : (((k + m - 1 : ℕ) : ℝ) + 2) * epsilon ≤ (σ : ℝ) := by
    rw [hcast]
    exact hbudget
  exact weighted_curve_inequality
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg)
    a hrows hgeneral z c hcY hcenters hz w v hw hv t ht θ w₀ v₀ hθ hv₀ hW hV
    σ hσ epsilon hepsilon hvol (k + m - 1)
    (MultivariateCurveConstancy.coordinateKernel_height_eq z hgen htrdeg).le
    hbudget' hseparated hgap hdiscount
    (centerPlaces z c hz (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg))
    (centerIndex (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg) z c hz)
    (centerIndex_centered (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg) z c hz)
    (fun p _ => PlaceLocalRing.residue_integral htrdeg.le p)

end
end GeneralizedLogarithms.MultivariateCurveInterpolation

/-- info: 'GeneralizedLogarithms.MultivariateCurveInterpolation.weighted_curve_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveInterpolation.weighted_curve_inequality

/-- info: 'GeneralizedLogarithms.MultivariateCurveInterpolation.intrinsic_weighted_curve_inequality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveInterpolation.intrinsic_weighted_curve_inequality
