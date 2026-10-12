import GeneralizedLogarithms.MultivariateCurveModels
import GeneralizedLogarithms.MultivariateGeometryScale
import LogIrrationalityMeasure.Ampleness.BlowupAmpleTwist
import LogIrrationalityMeasure.Ampleness.NumericalAmplenessTheorem
import LogIrrationalityMeasure.Ampleness.BlowupJetSurjectivityComplete

/-!
# Geometric generation of degree-controlled multilogarithmic jets

The explicit numerical conditions yield a uniform margin for every curve in
the blowup. The ample large twist is constructed independently. Numerical
ampleness and the original blowup-to-jets theorem then supply actual polynomial
interpolation at every sufficiently large integral multiple of a common radius.
Neither ampleness nor geometric jet generation is assumed in the final theorem.
-/

namespace GeneralizedLogarithms.MultivariateGeometricInterpolation

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open LogIrrationalityMeasure LogExponent
open LogExponentSeshadri.Geometry NumericalAmpleness
open MultivariateGeometryScale MultivariateCompactLogJetIdeal

variable {k m : ℕ} {K : Type} [Fintype K]
variable {w v : Fin k ⊕ Fin m → ℚ}

theorem centerIdeal_support_ne_top (hk : 0 < k) (s : Scale w v)
    (a : Fin m → Fin k → ℤ) (c : K → Fin k ⊕ Fin m → ℂ)
    (hcY : ∀ b r, c b (Sum.inl r) ≠ 0) : (s.centerIdeal a c).support ≠ ⊤ := by
  classical
  let o : affineSpace k m := MultivariateCompactJetPolynomial.centerPoint 0
  have havoid : s.affineChart o ∉ (s.centerIdeal a c).support := by
    change s.affineChart o ∉ ((s.centerIdeal a c).support : Set s.compactification)
    rw [s.centerIdeal_support a c hcY]
    intro h
    obtain ⟨b, z, hz⟩ := Set.mem_iUnion.mp h
    have he : point (c b) z = o := s.affineChart.isOpenEmbedding.injective hz
    have hc : point (c b) z = MultivariateCompactJetPolynomial.centerPoint (c b) := by
      have hh := Set.mem_range_self (f := point (c b)) z
      rw [range_point] at hh
      exact hh
    have hx : MvPolynomial.X (Sum.inl (⟨0, hk⟩ : Fin k)) ∈ o.asIdeal := by
      change MvPolynomial.aeval (0 : Fin k ⊕ Fin m → ℂ) _ = 0
      simp
    rw [he.symm.trans hc] at hx
    change MvPolynomial.aeval (c b) (MvPolynomial.X (Sum.inl (⟨0, hk⟩ : Fin k))) = 0 at hx
    simp only [MvPolynomial.aeval_X] at hx
    exact hcY b ⟨0, hk⟩ hx
  intro h
  exact havoid (by rw [h]; trivial)

variable [LinearOrder (Fin k ⊕ Fin m)]
variable {a : Fin m → Fin k → ℤ} {c : K → Fin k ⊕ Fin m → ℂ}

/-- The desired blowup bundle is ample, using all three curve cases and a
separately constructed ample large twist. -/
theorem blowupBundle_ample (hk : 0 < k) (d : MultivariateCurveMargin.NumericalData a c)
    (s : Scale d.w d.v) :
    (BlowupJetSurjectivity.blowupBundle (s.centerIdeal a c) s.hyperplane).IsAmple := by
  classical
  let I := s.centerIdeal a c
  let π := LogExponentSeshadri.BlowupGluing.projection I
  let p := π ≫ s.compactificationStructureMap
  let A := s.hyperplane.pullback π
  let L := LogExponentSeshadri.BlowupGluing.exceptionalLineBundle I
  let ι := LogExponentSeshadri.BlowupGluing.exceptionalInclusion I
  have hL : PresentsPullbackIdeal I π L ι :=
    LogExponentSeshadri.BlowupGluing.exceptional_presents I
  let : IsProper p := by dsimp [p, π]; infer_instance
  obtain ⟨q, hq, hample⟩ := LogExponentSeshadri.BlowupGluing.exists_ample_exceptional_power_gt_one
    I (centerIdeal_support_ne_top hk s a c d.centerY_nonzero) s.hyperplane s.hyperplane_ample
  have hσ : (0 : ℝ) < d.sigma := by exact_mod_cast d.sigma_pos
  have hmargin (C : IntegralCurve (LogExponentSeshadri.BlowupGluing.scheme I)) :
      BlowupCurveMargin.marginCoefficient q d.sigma *
        (curveDegree p ((A.pow q).tensor L) C : ℝ) ≤
          (curveDegree p (A.tensor L) C : ℝ) := by
    by_cases hc : ∃ x : s.compactification, Set.range (C.embedding ≫ π) ⊆ {x}
    · obtain ⟨x, hx⟩ := hc
      exact BlowupCurveMargin.margin_of_contracted p π s.hyperplane L
        q hq hample d.sigma hσ C x hx
    · by_cases hm : ∃ x : C.scheme, (C.embedding ≫ π) x ∈ s.affineChart.opensRange
      · have h := MultivariateCurveModels.margin_of_noncontracted_meets_chart d
          s.exponents s.constantIndex s.exponents_constant s.coordinateIndex s.exponents_coordinate
          (s.radius : ℚ) (by exact_mod_cast s.radius_pos) s.degreePowers s.degreePowers_eq
          s.pureIndex s.exponents_pure
          (fun b => by simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm]
            using s.budget d.w_pos b) (logCutoff d.v)
          (logCutoff_strict d.v d.v_pos) s.jetPowers s.jetPowers_pos s.jetPowers_eq
          π (LogExponentSeshadri.BlowupGluing.isBlowup I) L ι hL q hq hample C hc hm
        exact h.2
      · exact BlowupCurveMargin.margin_of_image_outside_chart p I π A L ι hL q hq hample
          d.sigma hσ C s.affineChart.opensRange
          (s.centerIdeal_support_subset_chart a c d.centerY_nonzero) (fun x hx => hm ⟨x, hx⟩)
  have htarget : (A.tensor L).IsAmple :=
    isAmple_of_uniform_curve_margin p ((A.pow q).tensor L) (A.tensor L) hample
      (BlowupCurveMargin.marginCoefficient q d.sigma)
      (BlowupCurveMargin.marginCoefficient_pos hq hσ) hmargin
  exact AmpleIso.isAmple_of_sheaf_iso (A.tensor L)
    (BlowupJetSurjectivity.blowupBundle I s.hyperplane)
    (moduleTensorComm A.sheaf L.sheaf) htarget

theorem eventual_jetRestriction_surjective (hk : 0 < k)
    (d : MultivariateCurveMargin.NumericalData a c) (s : Scale d.w d.v) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective
      (BlowupJetSurjectivity.jetRestriction (s.centerIdeal a c) s.hyperplane n) := by
  obtain ⟨N, hN⟩ := BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective
    s.compactificationStructureMap (s.centerIdeal a c) s.hyperplane (blowupBundle_ample hk d s)
  exact eventually_atTop.mpr ⟨N, hN⟩

/-- Actual multilogarithmic interpolation along a cofinal integral scale.
All geometric generation and polynomial degree-control inputs are discharged;
the explicit numerical curve conditions remain. -/
theorem eventual_weighted_packets (hk : 0 < k)
    (d : MultivariateCurveMargin.NumericalData a c) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
      Function.Surjective (fun P : {P : MvPolynomial (Fin k ⊕ Fin m) ℂ //
          WeightedSliceDegree.SupportBound (fun j => (d.w j : ℝ)) ((n : ℝ) * R) P} =>
        fun b => JetGeometry.rationalCoefficientPacket d.v (n * R)
          (MultivariateFormalJet.formalJet a (c b) P.val)) := by
  let s := chooseScale d.w d.v d.w_pos d.v_pos
  refine ⟨s.radius, s.radius_pos, ?_⟩
  have hc : Function.Injective c := by
    intro i j hij
    apply d.centers_injective
    exact congrArg (fun f => fun r => f (Sum.inl r)) hij
  exact s.eventual_weighted_packets d.w_pos d.v_pos a c hc d.centerY_nonzero
    (eventual_jetRestriction_surjective hk d s)

end
end GeneralizedLogarithms.MultivariateGeometricInterpolation

/-- info: 'GeneralizedLogarithms.MultivariateGeometricInterpolation.blowupBundle_ample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateGeometricInterpolation.blowupBundle_ample

/-- info: 'GeneralizedLogarithms.MultivariateGeometricInterpolation.eventual_weighted_packets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateGeometricInterpolation.eventual_weighted_packets
