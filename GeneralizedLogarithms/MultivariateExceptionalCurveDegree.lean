import GeneralizedLogarithms.MultivariateCompactLogJetIdeal
import GeneralizedLogarithms.MultifibreInequality
import LogIrrationalityMeasure.Ampleness.ExceptionalCurveDegree

/-!
# Exceptional line bundle degree from actual multilogarithmic contacts

The compactified product ideal has its explicitly calculated DVR colength at
every centered place. The generic divisor-length formula then identifies the
degree of a line bundle presenting its pullback with the negative contact sum.
No local length or contact identity is taken as a hypothesis.
-/

namespace GeneralizedLogarithms.MultivariateExceptionalCurveDegree

noncomputable section

open scoped BigOperators
open AlgebraicGeometry CategoryTheory TopologicalSpace
open LogIrrationalityMeasure
open LogExponent LogExponentSeshadri.Geometry LogExponentSeshadri.Frames
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open CurveCenters PlaceValuationRing
open ExceptionalCurveDegree
open MultivariateCompactLogJetIdeal MultivariateLogPolynomialAdapter
open MultivariateJetProductLocalization

variable {X Y : Scheme.{0}} {k m : ℕ}

theorem localIdeal_compactIdeal {A : Type} [CommRing A] {K : Type*} [Fintype K]
    (a : Fin m → Fin k → ℤ) (c : K → Fin k ⊕ Fin m → ℂ)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ)
    (j : affineSpace k m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (φ : coordinateRing k m →+* A) :
    localIdeal (compactIdeal a c T e j) (Spec.map (CommRingCat.ofHom φ) ≫ j) =
      (polynomialIdeal a c T e).map φ := by
  unfold localIdeal
  rw [Scheme.IdealSheafData.comap_comp, restrict_compactIdeal]
  exact localIdeal_specIdeal _ φ

section Curve

variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem map_logPowerIdeal_eq_top_of_transcendental
    (a : Fin m → Fin k → ℤ) (z : Fin k ⊕ Fin m → E)
    (hz : ∃ i, Transcendental ℂ (z i)) (c : Fin k ⊕ Fin m → ℂ)
    (hcY : ∀ r, c (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) :
    (logPowerIdeal a c T e).map (MvPolynomial.aeval z).toRingHom = ⊤ := by
  classical
  have hn : ∃ i, MvPolynomial.aeval z
      (MultivariateCompactJetPolynomial.coordinates c (logPolynomials a T) i) ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Ideal.span (Set.range
        (MultivariateCompactJetPolynomial.coordinates c (logPolynomials a T))) ≤
        RingHom.ker (MvPolynomial.aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    rw [MultivariateCompactJetPolynomial.span_coordinates c hcY _
      (logPolynomials_aeval_zero a T)] at hle
    obtain ⟨i, hi⟩ := hz
    have hc : MvPolynomial.X i - MvPolynomial.C (c i) ∈ WeightedBezout.pointIdeal c := by
      change MvPolynomial.aeval c _ = 0
      simp
    have he := hle hc
    change MvPolynomial.aeval z _ = 0 at he
    simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero] at he
    exact hi (he ▸ isAlgebraic_algebraMap (c i))
  obtain ⟨i, hi⟩ := hn
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (show
      MultivariateCompactJetPolynomial.coordinates c (logPolynomials a T) i ^ e i ∈
        logPowerIdeal a c T e from Ideal.subset_span (Set.mem_range_self i)))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow]
  exact (isUnit_iff_ne_zero.mpr hi).pow (e i)

theorem compactIdeal_comap_ne_bot_of_generic {K : Type*} [Fintype K]
    (a : Fin m → Fin k → ℤ) (c : K → Fin k ⊕ Fin m → ℂ)
    (hcY : ∀ b r, c b (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ)
    (j : affineSpace k m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin k ⊕ Fin m → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j) :
    (compactIdeal a c T e j).comap g ≠ ⊥ := by
  have htop : localIdeal (compactIdeal a c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊤ := by
    rw [hgeneric, localIdeal_compactIdeal]
    unfold polynomialIdeal
    change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
    rw [map_prod]
    have ht : ∀ b : K, (logPowerIdeal a (c b) T e).map
        (MvPolynomial.aeval z).toRingHom = ⊤ :=
      fun b => map_logPowerIdeal_eq_top_of_transcendental a z hz (c b) (hcY b) T e
    simp only [Ideal.mapHom_apply, ht]
    rw [← Ideal.one_eq_top]
    exact Finset.prod_const_one
  intro hzero
  have hb : localIdeal (compactIdeal a c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊥ := by
    simp only [localIdeal, Scheme.IdealSheafData.comap_comp, hzero,
      Scheme.IdealSheafData.comap_bot]
    exact Ideal.map_bot
  exact bot_ne_top (hb.symm.trans htop)

theorem centerMorphism_eq_centeredLift [X.IsSeparated]
    (j : affineSpace k m ⟶ X) (g : parameterCurve f hf ⟶ X)
    (z : Fin k ⊕ Fin m → E)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E) (c : Fin k ⊕ Fin m → ℂ) (hc : Centered z c p) :
    centerMorphism f hf p ≫ g = Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (PlaceCenteredBranch.lift p z c hc)).toRingHom) ≫ j := by
  apply centerMorphism_comp_eq_of_generic f hf p g
  rw [hgeneric, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  exact PlaceCenteredBranch.lift_aeval p z c hc P

theorem centered_of_closedPoint_eq (p : NormalizedPlace ℂ E)
    (z : Fin k ⊕ Fin m → E) (c : Fin k ⊕ Fin m → ℂ)
    (j : affineSpace k m ⟶ X) [IsOpenImmersion j]
    (q : Spec (CommRingCat.of (ring p)) ⟶ X)
    (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫ q =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hclosed : q (IsLocalRing.closedPoint (ring p)) =
      j (MultivariateCompactJetPolynomial.centerPoint c)) : Centered z c p := by
  have hr : Set.range q ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map q.continuous).mem_open
      j.isOpenEmbedding.isOpen_range
        (hclosed ▸ Set.mem_range_self (MultivariateCompactJetPolynomial.centerPoint c))
  let g := IsOpenImmersion.lift j q hr
  have hg : g ≫ j = q := IsOpenImmersion.lift_fac j q hr
  let φ : coordinateRing k m →+* ring p := (Spec.preimage g).hom
  have hgφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
  have hcomp : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap (ring p) E) =
      CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgφ]
    apply (cancel_mono j).mp
    rw [Category.assoc, hg]
    exact hgeneric
  have hgc : g (IsLocalRing.closedPoint (ring p)) =
      MultivariateCompactJetPolynomial.centerPoint c := by
    apply j.isOpenEmbedding.injective
    change (g ≫ j) (IsLocalRing.closedPoint (ring p)) = _
    rw [hg, hclosed]
  have hcomap : PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p)) =
      MultivariateCompactJetPolynomial.centerPoint c := by
    change (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint (ring p)) = _
    rw [hgφ, hgc]
  intro i
  let P : coordinateRing k m := MvPolynomial.X i - MvPolynomial.C (c i)
  have hmem : φ P ∈ IsLocalRing.maximalIdeal (ring p) := by
    change P ∈ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p))).asIdeal
    rw [hcomap]
    change P ∈ WeightedBezout.pointIdeal c
    rw [WeightedBezout.mem_pointIdeal]
    simp [P]
  have hpos := p.valuation.toValuation.mem_maximalIdeal_iff.mp hmem
  have heval := congrArg
    (fun φ : CommRingCat.of (coordinateRing k m) ⟶ CommRingCat.of E => φ P) hcomp
  change algebraMap (ring p) E (φ P) = MvPolynomial.aeval z P at heval
  change 0 < p.valuation (algebraMap (ring p) E (φ P)) at hpos
  rw [heval] at hpos
  simpa [P] using hpos

theorem localIdeal_length_eq_placeContact [X.IsSeparated] {K : Type*} [Fintype K]
    (a : Fin m → Fin k → ℤ) (c : K → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective (fun b r => c b (Sum.inl r)))
    (hcY : ∀ b r, c b (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r))
    (j : affineSpace k m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin k ⊕ Fin m → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (b : K) (hcenter : Centered z (c b) p) :
    ((Module.length (ring p) ((ring p) ⧸
      localIdeal (compactIdeal a c T e j) (centerMorphism f hf p ≫ g))).toNat : ℚ) =
      R * MultilogBranchCoordinates.placeContact p a z (c b) (hcY b) hcenter
        (Centered.exists_nonzero_difference z (c b) hz) v := by
  rw [centerMorphism_eq_centeredLift f hf j g z hgeneric p (c b) hcenter,
    localIdeal_compactIdeal]
  exact polynomialIdeal_colength_eq_placeContact p v hv a c hc hcY z b hcenter
    (Centered.exists_nonzero_difference z (c b) hz) T hT R e he

/-- The exceptional degree formula over the full finite family of centered
places. The caller's center witnesses can be those in the curve inequality. -/
theorem compactIdeal_degree_eq_neg_contact_sum [X.IsSeparated] {K : Type*} [Fintype K]
    (a : Fin m → Fin k → ℤ) (c : K → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective (fun b r => c b (Sum.inl r)))
    (hcY : ∀ b r, c b (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : Fin k ⊕ Fin m → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r))
    (j : affineSpace k m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (pX : X ⟶ base) [IsSeparated pX] (hj : j ≫ pX = structureMap k m)
    (π : Y ⟶ X) (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (hL : PresentsPullbackIdeal (compactIdeal a c T e j) π L ι)
    (g : parameterCurve f hf ⟶ Y) (z : Fin k ⊕ Fin m → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ π =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hfinite : ∀ t : E, Transcendental ℂ t →
      FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
    (index : ∀ p, p ∈ centerPlaces z c hz hfinite → K)
    (hcenter : ∀ p (hp : p ∈ centerPlaces z c hz hfinite), Centered z (c (index p hp)) p)
    (hres : ∀ p ∈ centerPlaces z c hz hfinite,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -R * ∑ p ∈ centerPlaces z c hz hfinite,
        MultifibreInequality.contact a z c hcY hz v (centerPlaces z c hz hfinite)
          index hcenter hres p := by
  classical
  let I := compactIdeal a c T e j
  have hg : I.comap (g ≫ π) ≠ ⊥ :=
    compactIdeal_comap_ne_bot_of_generic f hf a c hcY T e j (g ≫ π) z hz hgeneric
  let D := idealDivisor f hf I π L ι hL g hg
  let S := centerPlaces z c hz hfinite
  let μ := MultifibreInequality.contact a z c hcY hz v S index hcenter hres
  have hzero (p : NormalizedPlace ℂ E) (hp : p ∉ S) : D p = 0 := by
    have havoid : (centerMorphism f hf p ≫ g ≫ π)
        (IsLocalRing.closedPoint (ring p)) ∉ I.support := by
      intro hmem
      change _ ∈ ((compactIdeal a c T e j).support : Set X) at hmem
      rw [support_compactIdeal a c hcY T e hepos j pX hj] at hmem
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨t, ht⟩ := hb
      have hpoint : point (c b) t = MultivariateCompactJetPolynomial.centerPoint (c b) := by
        have h := Set.mem_range_self (f := point (c b)) t
        rw [range_point] at h
        exact h
      have hclosed : (centerMorphism f hf p ≫ g ≫ π)
          (IsLocalRing.closedPoint (ring p)) =
          j (MultivariateCompactJetPolynomial.centerPoint (c b)) :=
        ht.symm.trans (congrArg j hpoint)
      have hfield : Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫
          (centerMorphism f hf p ≫ g ≫ π) =
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
        rw [← Category.assoc, centerMorphism_generic]
        exact hgeneric
      apply hp
      exact (mem_centerPlaces z c hz hfinite p).mpr
        ⟨b, centered_of_closedPoint_eq p z (c b) j _ hfield hclosed⟩
    change idealDivisor f hf I π L ι hL g hg p = 0
    rw [idealDivisor_apply, localIdeal_eq_top_of_not_mem I _ havoid]
    simp
  have hsupport : D.support ⊆ S := by
    intro p hp
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (hzero p h)
  have hvalue (p : NormalizedPlace ℂ E) (hp : p ∈ S) : (D p : ℚ) = R * μ p := by
    letI := hres p hp
    have h := localIdeal_length_eq_placeContact f hf a c hc hcY T e v hv R he hT
      j (g ≫ π) z hz hgeneric p (index p hp) (hcenter p hp)
    change (idealDivisor f hf I π L ι hL g hg p : ℚ) = _
    rw [idealDivisor_apply]
    simpa only [MultifibreInequality.contact, dite_eq_left hp, I, μ] using h
  have hsum : D.sum (fun _ n => (n : ℚ)) = R * ∑ p ∈ S, μ p := by
    rw [D.sum_of_support_subset hsupport (fun _ n => (n : ℚ)) (by simp), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hvalue p hp)
  have hd := degree_eq_neg_idealDivisor_sum f hf I π L ι hL g hg
  have hdq : ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -D.sum (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun n : ℤ => (n : ℚ)) hd
  rw [hsum] at hdq
  simpa only [neg_mul, S, μ] using hdq

end Curve

end
end GeneralizedLogarithms.MultivariateExceptionalCurveDegree

/-- info: 'GeneralizedLogarithms.MultivariateExceptionalCurveDegree.centered_of_closedPoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateExceptionalCurveDegree.centered_of_closedPoint_eq

/-- info: 'GeneralizedLogarithms.MultivariateExceptionalCurveDegree.localIdeal_length_eq_placeContact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateExceptionalCurveDegree.localIdeal_length_eq_placeContact

/-- info: 'GeneralizedLogarithms.MultivariateExceptionalCurveDegree.compactIdeal_degree_eq_neg_contact_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateExceptionalCurveDegree.compactIdeal_degree_eq_neg_contact_sum
