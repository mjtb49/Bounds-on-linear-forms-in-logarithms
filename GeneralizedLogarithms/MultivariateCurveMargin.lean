import GeneralizedLogarithms.MultivariateCurveInterpolation
import GeneralizedLogarithms.MultivariateExceptionalCurveDegree
import LogIrrationalityMeasure.Geometry.CurveNormalizedDegreeTransfer
import LogIrrationalityMeasure.Ampleness.BlowupCurveMargin

/-!
# A curve margin computed from a genuine geometric model

For a normalized curve in a weighted monomial compactification, the polarization
degree and exceptional degree are computed from its actual coordinates and the
compactified multilogarithmic ideal. The intrinsic curve inequality gives the
nonnegative degree combination and hence a uniform margin. The desired degree
identities and margin are conclusions, not inputs.
-/

namespace GeneralizedLogarithms.MultivariateCurveMargin

noncomputable section

open scoped BigOperators
open AlgebraicGeometry CategoryTheory
open LogIrrationalityMeasure
open LogExponent LogExponentApprox LogExponentSeshadri.Geometry LogExponentSeshadri.Frames
open CurveNormalizationModel CurveCenters CurveValuationCenter PlaceValuationRing
open NumericalAmpleness
open MultivariateCurveInterpolation

variable {k m : ℕ} {K : Type} [Fintype K]
variable [frameOrder : LinearOrder (Fin k ⊕ Fin m)]

/-- Explicit arithmetic and weight conditions used by the intrinsic curve
inequality. This record contains no geometric degree or margin hypothesis. -/
structure NumericalData (a : Fin m → Fin k → ℤ) (c : K → Fin k ⊕ Fin m → ℂ) where
  rows_nonzero : ∀ i, a i ≠ 0
  general_position : IntegerGeneralPosition a
  centerY_nonzero : ∀ b r, c b (Sum.inl r) ≠ 0
  centers_injective : Function.Injective (fun b r => c b (Sum.inl r))
  w : Fin k ⊕ Fin m → ℚ
  v : Fin k ⊕ Fin m → ℚ
  w_pos : ∀ i, 0 < w i
  v_pos : ∀ i, 0 < v i
  t : Fin k ⊕ Fin m → ℝ
  t_pos : ∀ i, 0 < t i
  theta : ℝ
  w₀ : ℝ
  v₀ : ℝ
  theta_nonneg : 0 ≤ theta
  v₀_pos : 0 < v₀
  w_block : ∀ j, (w j : ℝ) =
    blockWeight (Finset.univ.image Sum.inr) (fun i => theta * t i) w₀ j
  v_block : ∀ j, (v j : ℝ) = blockWeight (Finset.univ.image Sum.inr) t v₀ j
  sigma : ℚ
  sigma_pos : 0 < sigma
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  volume : (Fintype.card K : ℝ) * (1 + 3 * (sigma : ℝ)) ^ (k + m) *
    (∏ j, (w j : ℝ)) / (∏ j, (v j : ℝ)) < 1
  budget : ((k + m : ℕ) + 1 : ℝ) * epsilon ≤ (sigma : ℝ)
  separated : ∀ A B : Finset (Fin k ⊕ Fin m), A.card = B.card →
    ∀ i : Fin m, Sum.inr i ∈ A → Sum.inr i ∉ B →
    (∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
      (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) →
    ((A.card : ℝ) ^ A.card / epsilon ^ A.card) * (∏ j ∈ B, (v j : ℝ)) <
      ∏ j ∈ A, (w j : ℝ)
  gap : ∀ r d : ℕ, r < k → 1 ≤ d - r → d - r ≤ k → d ≤ 2 * k - 1 →
    (d : ℝ) ^ d / epsilon ^ d < theta ^ r * (w₀ / v₀) ^ (d - r)
  discount : (1 + (sigma : ℝ)) * theta ≤ 1

variable {a : Fin m → Fin k → ℤ} {c : K → Fin k ⊕ Fin m → ℂ}

section Field

variable {E : Type} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]

def contactSum (d : NumericalData a c) (z : Fin k ⊕ Fin m → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let hz := nonconstant_coordinates z hgen htrdeg
  let S := centerPlaces z c hz hfinite
  ∑ p ∈ S, (MultifibreInequality.contact a z c d.centerY_nonzero hz d.v S
    (centerIndex hfinite z c hz) (centerIndex_centered hfinite z c hz)
    (fun p _ => PlaceLocalRing.residue_integral htrdeg.le p) p : ℝ)

def poleDegree (d : NumericalData a c) (z : Fin k ⊕ Fin m → E)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  CurveContactSum.weightedDegree
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg) z d.w

theorem actual_contact_bound (d : NumericalData a c) (z : Fin k ⊕ Fin m → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    (1 + (d.sigma : ℝ)) * contactSum d z hgen htrdeg ≤ poleDegree d z htrdeg :=
  intrinsic_weighted_curve_inequality a d.rows_nonzero d.general_position z hgen htrdeg
    c d.centerY_nonzero d.centers_injective d.w d.v d.w_pos d.v_pos d.t d.t_pos
    d.theta d.w₀ d.v₀ d.theta_nonneg d.v₀_pos d.w_block d.v_block
    d.sigma d.sigma_pos d.epsilon d.epsilon_pos d.volume d.budget d.separated d.gap d.discount

end Field

section Model

variable {B : Scheme.{0}} {E Ω : Type} [Field E] [Algebra ℂ E]
  [Algebra.EssFiniteType ℂ E] [Fintype Ω]

/-- For a supplied genuine curve model, compute both geometric degrees and
deduce the positive uniform margin against an independently ample large twist. -/
theorem margin_of_model (d : NumericalData a c)
    (s : Ω → (Fin k ⊕ Fin m) →₀ ℕ) (s₀ : Ω) (hs₀ : s s₀ = 0)
    (coordinate : (Fin k ⊕ Fin m) → Ω)
    (hcoordinate : ∀ i, s (coordinate i) = Finsupp.single i 1)
    (R : ℚ) (hR : 0 < R)
    (degreePowers : (Fin k ⊕ Fin m) → ℕ)
    (hdegreePowers : ∀ i, d.w i * (degreePowers i : ℚ) = R)
    (pure : (Fin k ⊕ Fin m) → Ω)
    (hpure : ∀ i, s (pure i) = Finsupp.single i (degreePowers i))
    (hbudget : ∀ b, (∑ i, d.w i * (s b i : ℚ)) ≤ R)
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, d.v (Sum.inr i) < (T i r : ℚ) * d.v (Sum.inl r))
    (e : (Fin k ⊕ Fin m) → ℕ) (hepos : ∀ i, 0 < e i)
    (he : ∀ i, d.v i * (e i : ℚ) = R)
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (π : B ⟶ Proj (WeightedCompactification.imageGrade (R := ℂ) s))
    (L : LineBundle B) (ι : L.sheaf ⟶ O B)
    (hL : PresentsPullbackIdeal
      (MultivariateCompactLogJetIdeal.compactIdeal a c T e
        (WeightedCompactification.affineChartMap s s₀ hs₀ coordinate hcoordinate)) π L ι)
    (q : ℕ) (hq : 1 < q)
    (hample : ((((WeightedCompactification.lineBundle (R := ℂ) s).pullback π).pow q).tensor L).IsAmple)
    (C : IntegralCurve B) (z : Fin k ⊕ Fin m → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ C.scheme) [IsFinite g]
    (hg : g ≫ C.embedding ≫ p = parameterCurveStructureMap f hf)
    (W : C.scheme.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)]
    (hgeneric : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ π) =
      CurveMonomialMap.genericMonomialMap s s₀ hs₀ coordinate hcoordinate z) :
    let A := (WeightedCompactification.lineBundle (R := ℂ) s).pullback π
    0 ≤ (curveDegree p A C : ℝ) + (1 + (d.sigma : ℝ)) * (curveDegree p L C : ℝ) ∧
      BlowupCurveMargin.marginCoefficient q d.sigma *
          (curveDegree p ((A.pow q).tensor L) C : ℝ) ≤
        (curveDegree p (A.tensor L) C : ℝ) := by
  classical
  let : Nonempty Ω := ⟨s₀⟩
  let A := (WeightedCompactification.lineBundle (R := ℂ) s).pullback π
  let H := (A.pow q).tensor L
  let j := WeightedCompactification.affineChartMap (R := ℂ) s s₀ hs₀ coordinate hcoordinate
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let hz := nonconstant_coordinates z hgen htrdeg
  let S := centerPlaces z c hz hfinite
  let index := centerIndex hfinite z c hz
  let hcenter := centerIndex_centered hfinite z c hz
  let hres := fun p (_ : p ∈ S) => PlaceLocalRing.residue_integral htrdeg.le p
  have hA : (curveDegree p A C : ℝ) = (R : ℝ) * poleDegree d z htrdeg :=
    CurveNormalizedDegreeTransfer.weighted_curveDegree s z s₀ hs₀ coordinate hcoordinate
      p H hample C f hf g hg W hW π hgeneric d.w d.w_pos hR
      degreePowers hdegreePowers pure hpure hbudget hfinite
  have heval : (MvPolynomial.aeval z).toRingHom =
      MvPolynomial.eval₂Hom (algebraMap ℂ E) z := by
    apply RingHom.ext
    intro P
    exact MvPolynomial.aeval_def z P
  have hgeneric' : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding) ≫ π =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
    simpa only [Category.assoc, CurveMonomialMap.genericMonomialMap, heval, j] using hgeneric
  have hJ : (curveDegree p L C : ℝ) = -(R : ℝ) * contactSum d z hgen htrdeg := by
    have hd := CurveNormalizedDegreeTransfer.curveDegree_eq_normalized
      p H hample C f hf g hg W hW L
    have hn := MultivariateExceptionalCurveDegree.compactIdeal_degree_eq_neg_contact_sum
      f hf a c d.centers_injective d.centerY_nonzero T e hepos d.v d.v_pos R he hT
      j (WeightedCompactification.projection s)
      (CurveMonomialMap.affineChartMap_projection s s₀ hs₀ coordinate hcoordinate)
      π L ι hL (g ≫ C.embedding) z hz hgeneric' hfinite index hcenter hres
    rw [hd]
    simpa only [contactSum, Rat.cast_intCast, Rat.cast_neg, Rat.cast_mul, Rat.cast_sum,
      hfinite, hz, S, index, hcenter, hres] using congrArg (fun x : ℚ => (x : ℝ)) hn
  have hn : 0 ≤ (curveDegree p A C : ℝ) +
      (1 + (d.sigma : ℝ)) * (curveDegree p L C : ℝ) := by
    rw [hA, hJ]
    have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR.le
    have h := mul_le_mul_of_nonneg_left (actual_contact_bound d z hgen htrdeg) hR'
    nlinarith
  refine ⟨hn, ?_⟩
  exact BlowupCurveMargin.margin_of_nonnegative_degree p A L q hq hample d.sigma
    (by exact_mod_cast d.sigma_pos) C hn

end Model

end
end GeneralizedLogarithms.MultivariateCurveMargin

/-- info: 'GeneralizedLogarithms.MultivariateCurveMargin.actual_contact_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveMargin.actual_contact_bound

/-- info: 'GeneralizedLogarithms.MultivariateCurveMargin.margin_of_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveMargin.margin_of_model
