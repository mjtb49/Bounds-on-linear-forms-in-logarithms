import GeneralizedLogarithms.MultivariateCurveMargin
import LogIrrationalityMeasure.Ampleness.CurveBlowupImage
import LogIrrationalityMeasure.Geometry.CurveImageAffineChart
import LogIrrationalityMeasure.Geometry.CurveNormalizationMorphism

/-!
# Constructing the curve models needed by the multivariate margin

A noncontracted curve in the blowup meets the complement of the finite center
support. The blowup is an isomorphism there, so its function field is identified
with that of its image. The affine image coordinates generate this field; its
dimension gives transcendence degree one. Normalization supplies the finite
curve model and the generic coordinate identity used by the margin theorem.
-/

namespace GeneralizedLogarithms.MultivariateCurveModels

noncomputable section

open scoped BigOperators
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogIrrationalityMeasure
open LogExponent LogExponentSeshadri.Geometry LogExponentSeshadri.Frames
open CurveNormalizationModel CurveBlowupImage CurveImageAffineCoordinates
open MultivariateCompactLogJetIdeal NumericalAmpleness

variable {X B : Scheme.{0}} {k m : ℕ}

/-- Genuine geometric inputs for the curve margin; the existence theorem below
constructs them from a noncontracted curve meeting the affine chart. -/
structure ModelData (pX : X ⟶ Spec (.of ℂ)) (π : B ⟶ X)
    (j : affineSpace k m ⟶ X) (C : IntegralCurve B) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  coordinates : Fin k ⊕ Fin m → E
  coordinates_generate : IntermediateField.adjoin ℂ (Set.range coordinates) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  parameter : E
  parameter_transcendental : Transcendental ℂ parameter
  [parameterFinite : FiniteDimensional (IntermediateField.adjoin ℂ {parameter}) E]
  normalization : parameterCurve parameter parameter_transcendental ⟶ C.scheme
  [normalizationFinite : IsFinite normalization]
  normalization_over : normalization ≫ C.embedding ≫ π ≫ pX =
    parameterCurveStructureMap parameter parameter_transcendental
  chart : C.scheme.Opens
  chart_nonempty : chart ≠ ⊥
  [chartIso : IsIso (normalization ∣_ chart)]
  generic_coordinates : parameterCurveGenericPoint parameter parameter_transcendental ≫
    (normalization ≫ C.embedding ≫ π) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval coordinates).toRingHom) ≫ j

theorem center_point_isClosed {K : Type} [Fintype K]
    (a : Fin m → Fin k → ℤ) (c : K → Fin k ⊕ Fin m → ℂ)
    (hcY : ∀ b r, c b (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (hepos : ∀ i, 0 < e i)
    (pX : X ⟶ Spec (.of ℂ)) [IsProper pX]
    (j : affineSpace k m ⟶ X) [QuasiCompact j]
    (hj : j ≫ pX = structureMap k m)
    (x : X) (hx : x ∈ (compactIdeal a c T e j).support) : IsClosed ({x} : Set X) := by
  change x ∈ ((compactIdeal a c T e j).support : Set X) at hx
  rw [support_compactIdeal a c hcY T e hepos j pX hj] at hx
  obtain ⟨b, t, rfl⟩ := Set.mem_iUnion.mp hx
  let q := point (c b) ≫ j
  let : IsClosedImmersion q := CompactJetIdeal.section_isClosedImmersion pX q (by
    dsimp [q]
    rw [Category.assoc, hj, point_section])
  have he : Set.range q = {q t} := by
    ext x
    constructor
    · rintro ⟨t', rfl⟩
      exact congrArg q (Subsingleton.elim t' t)
    · rintro rfl
      exact ⟨t, rfl⟩
  rw [← he]
  exact q.isClosedEmbedding.isClosed_range

/-- Construction of generated coordinates and a finite normalization from the
actual blowup and its affine chart, without assuming the target model data. -/
theorem existsModelData {K : Type} [Fintype K]
    (a : Fin m → Fin k → ℤ) (c : K → Fin k ⊕ Fin m → ℂ)
    (hcY : ∀ b r, c b (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (hepos : ∀ i, 0 < e i)
    (pX : X ⟶ Spec (.of ℂ)) [IsProper pX]
    (j : affineSpace k m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hj : j ≫ pX = structureMap k m)
    (π : B ⟶ X) [IsProper π] (hπ : IsBlowup (compactIdeal a c T e j) π)
    (C : IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (hm : ∃ x : C.scheme, (C.embedding ≫ π) x ∈ j.opensRange) :
    Nonempty (ModelData pX π j C) := by
  classical
  let I := compactIdeal a c T e j
  have hU : ∃ x : C.scheme, (C.embedding ≫ π) x ∈ I.support.compl :=
    exists_image_outside_closed_points (C.embedding ≫ π) I.support
      (center_point_isClosed a c hcY T e hepos pX j hj) hn
  let : IsIso (π ∣_ I.support.compl) := blowup_restrict_isIso hπ
  let D := imageCurve π C hn
  let pD := D.embedding ≫ pX
  let pC := C.embedding ≫ π ≫ pX
  let := IntegralAffineOpenDimension.functionFieldAlgebra pD
  let := IntegralAffineOpenDimension.functionFieldAlgebra pC
  let fi := imageFunctionFieldIso π C hn I.support.compl hU
  have hfi := imageFunctionFieldIso_generic π C hn I.support.compl hU
  let fe : D.scheme.functionField ≃ₐ[ℂ] C.scheme.functionField :=
    fieldAlgEquiv pD pC fi (by
      simpa only [pD, pC, Category.assoc] using congrArg (fun f => f ≫ pX) hfi)
  let U := affinePart D.embedding j
  let q := affinePresentation D.embedding j
  have hmeet : ∃ x : D.scheme, D.embedding x ∈ j.opensRange := by
    obtain ⟨x, hx⟩ := hm
    refine ⟨imageMap π C hn x, ?_⟩
    change (imageCurve π C hn).embedding (imageMap π C hn x) ∈ j.opensRange
    simpa only [← Scheme.Hom.comp_apply, imageMap_comp] using hx
  let : Nonempty U.1 := affinePart_nonempty D.embedding j hmeet
  let zD : Fin k ⊕ Fin m → D.scheme.functionField :=
    CurveImageAffineCoordinates.coordinates U q
  let z : Fin k ⊕ Fin m → C.scheme.functionField := fe ∘ zD
  have hq := affinePresentation_over pX D.embedding j hj
  obtain ⟨hftD, htrdegD, hgenD⟩ := CurveImageAffineCoordinates.field_properties
    pD D.dimension U q hq
  let := hftD
  obtain ⟨hft, htrdeg, hgen⟩ := transport_field_properties fe zD htrdegD hgenD
  let := hft
  have hzmap : Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j =
      C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ π := by
    have himage := CurveImageAffineCoordinates.coordinates_generic_map pD U q hq j
      D.embedding (affinePresentation_comp D.embedding j)
    have he : (MvPolynomial.aeval z : MvPolynomial (Fin k ⊕ Fin m) ℂ →ₐ[ℂ]
        C.scheme.functionField).toRingHom = fi.hom.hom.comp
        (MvPolynomial.aeval zD : MvPolynomial (Fin k ⊕ Fin m) ℂ →ₐ[ℂ]
          D.scheme.functionField).toRingHom := by
      apply congrArg AlgHom.toRingHom
        (show MvPolynomial.aeval z = fe.toAlgHom.comp (MvPolynomial.aeval zD) from ?_)
      apply MvPolynomial.algHom_ext
      intro i
      simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
      rfl
    rw [he, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
    rw [show Spec.map (CommRingCat.ofHom (MvPolynomial.aeval zD).toRingHom) ≫ j =
      D.scheme.fromSpecStalk (genericPoint D.scheme) ≫ D.embedding from himage]
    exact hfi
  have hfinite := CurveParameterFinite.finite_over_every_parameter ℂ C.scheme.functionField htrdeg
  obtain ⟨i, hi⟩ := MultivariateCurveInterpolation.nonconstant_coordinates z hgen htrdeg
  let f := z i
  have hf : Transcendental ℂ f := hi
  let := hfinite f hf
  obtain ⟨g, hg, hgeneric, hgfinite, W, hW, hWiso⟩ :=
    CurveNormalizationMorphism.exists_intrinsic_normalization_morphism pC C.dimension f hf
  let := hgfinite
  let := hWiso
  have hWne : W ≠ ⊥ := by
    intro he
    simp only [he, Opens.mem_bot] at hW
  have hc : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ π) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
    rw [← Category.assoc, ← Category.assoc, hgeneric]
    exact hzmap.symm
  exact ⟨{ E := C.scheme.functionField
           field := inferInstance
           algebra := inferInstance
           essFiniteType := hft
           coordinates := z
           coordinates_generate := hgen
           trdeg_one := htrdeg
           parameter := f
           parameter_transcendental := hf
           parameterFinite := inferInstance
           normalization := g
           normalizationFinite := hgfinite
           normalization_over := hg
           chart := W
           chart_nonempty := hWne
           chartIso := hWiso
           generic_coordinates := hc }⟩

section Margin

variable {K Ω : Type} [Fintype K] [Fintype Ω]
  [LinearOrder (Fin k ⊕ Fin m)]
variable {a : Fin m → Fin k → ℤ} {c : K → Fin k ⊕ Fin m → ℂ}

/-- Every noncontracted curve meeting the affine chart has the actual
multivariate margin; all its field and normalization data are constructed. -/
theorem margin_of_noncontracted_meets_chart (d : MultivariateCurveMargin.NumericalData a c)
    (s : Ω → (Fin k ⊕ Fin m) →₀ ℕ) (s₀ : Ω) (hs₀ : s s₀ = 0)
    (coordinate : (Fin k ⊕ Fin m) → Ω)
    (hcoordinate : ∀ i, s (coordinate i) = Finsupp.single i 1)
    (R : ℚ) (hR : 0 < R) (degreePowers : (Fin k ⊕ Fin m) → ℕ)
    (hdegreePowers : ∀ i, d.w i * (degreePowers i : ℚ) = R)
    (pure : (Fin k ⊕ Fin m) → Ω)
    (hpure : ∀ i, s (pure i) = Finsupp.single i (degreePowers i))
    (hbudget : ∀ b, (∑ i, d.w i * (s b i : ℚ)) ≤ R)
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, d.v (Sum.inr i) < (T i r : ℚ) * d.v (Sum.inl r))
    (e : (Fin k ⊕ Fin m) → ℕ) (hepos : ∀ i, 0 < e i)
    (he : ∀ i, d.v i * (e i : ℚ) = R)
    (π : B ⟶ Proj (WeightedCompactification.imageGrade (R := ℂ) s)) [IsProper π]
    (hπ : IsBlowup (compactIdeal a c T e
      (WeightedCompactification.affineChartMap s s₀ hs₀ coordinate hcoordinate)) π)
    (L : LineBundle B) (ι : L.sheaf ⟶ O B)
    (hL : PresentsPullbackIdeal (compactIdeal a c T e
      (WeightedCompactification.affineChartMap s s₀ hs₀ coordinate hcoordinate)) π L ι)
    (q : ℕ) (hq : 1 < q)
    (hample : ((((WeightedCompactification.lineBundle (R := ℂ) s).pullback π).pow q).tensor L).IsAmple)
    (C : IntegralCurve B)
    (hn : ¬ ∃ x, Set.range (C.embedding ≫ π) ⊆ {x})
    (hm : ∃ x : C.scheme, (C.embedding ≫ π) x ∈
      (WeightedCompactification.affineChartMap s s₀ hs₀ coordinate hcoordinate).opensRange) :
    let p := π ≫ WeightedCompactification.projection s
    let A := (WeightedCompactification.lineBundle (R := ℂ) s).pullback π
    0 ≤ (curveDegree p A C : ℝ) + (1 + (d.sigma : ℝ)) * (curveDegree p L C : ℝ) ∧
      BlowupCurveMargin.marginCoefficient q d.sigma *
          (curveDegree p ((A.pow q).tensor L) C : ℝ) ≤
        (curveDegree p (A.tensor L) C : ℝ) := by
  classical
  let : Nonempty Ω := ⟨s₀⟩
  obtain ⟨r⟩ := existsModelData a c d.centerY_nonzero T e hepos
    (WeightedCompactification.projection s)
    (WeightedCompactification.affineChartMap s s₀ hs₀ coordinate hcoordinate)
    (CurveMonomialMap.affineChartMap_projection s s₀ hs₀ coordinate hcoordinate)
    π hπ C hn hm
  let := r.field
  let := r.algebra
  let := r.essFiniteType
  let := r.parameterFinite
  let := r.normalizationFinite
  let := r.chartIso
  have hgeneric : parameterCurveGenericPoint r.parameter r.parameter_transcendental ≫
      (r.normalization ≫ C.embedding ≫ π) =
      CurveMonomialMap.genericMonomialMap s s₀ hs₀ coordinate hcoordinate r.coordinates := by
    have heval : (MvPolynomial.aeval r.coordinates).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap ℂ r.E) r.coordinates := by
      apply RingHom.ext
      intro P
      exact MvPolynomial.aeval_def r.coordinates P
    simpa only [CurveMonomialMap.genericMonomialMap, heval] using r.generic_coordinates
  exact MultivariateCurveMargin.margin_of_model d s s₀ hs₀ coordinate hcoordinate R hR
    degreePowers hdegreePowers pure hpure hbudget T hT e hepos he
    (π ≫ WeightedCompactification.projection s) π L ι hL q hq hample C r.coordinates
    r.coordinates_generate r.trdeg_one r.parameter r.parameter_transcendental
    r.normalization r.normalization_over r.chart r.chart_nonempty hgeneric

end Margin

end
end GeneralizedLogarithms.MultivariateCurveModels

/-- info: 'GeneralizedLogarithms.MultivariateCurveModels.existsModelData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveModels.existsModelData

/-- info: 'GeneralizedLogarithms.MultivariateCurveModels.margin_of_noncontracted_meets_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateCurveModels.margin_of_noncontracted_meets_chart
