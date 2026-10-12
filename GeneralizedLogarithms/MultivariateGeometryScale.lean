import GeneralizedLogarithms.MultivariateAffineJetFramedPackets
import GeneralizedLogarithms.MultivariateCompactLogJetIdeal
import LogIrrationalityMeasure.Approximation.WeightedGeometryScale
import LogIrrationalityMeasure.Ampleness.WeightedProjectiveAmple
import LogIrrationalityMeasure.Geometry.CurveMonomialMap

/-!
# A finite weighted compactification for multilogarithmic jets

A common integral radius simultaneously clears positive rational degree and
jet weights. The finite monomial system consists of the constant monomial,
the coordinates and the required pure powers. It gives a proper monomial
compactification with a genuinely ample hyperplane bundle. The compactified
center ideal has the required affine restriction and finite affine support.
The final interpolation theorem still assumes eventual geometric jet generation.
-/

namespace GeneralizedLogarithms.MultivariateGeometryScale

noncomputable section
open scoped BigOperators
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open LogIrrationalityMeasure
open LogExponent LogExponentSeshadri.Geometry
open MultivariateCompactLogJetIdeal

variable {k m : ℕ}

structure Scale (w v : Fin k ⊕ Fin m → ℚ) where
  radius : ℕ
  radius_pos : 0 < radius
  degreePowers : Fin k ⊕ Fin m → ℕ
  jetPowers : Fin k ⊕ Fin m → ℕ
  degreePowers_pos : ∀ j, 0 < degreePowers j
  jetPowers_pos : ∀ j, 0 < jetPowers j
  degreePowers_eq : ∀ j, w j * (degreePowers j : ℚ) = radius
  jetPowers_eq : ∀ j, v j * (jetPowers j : ℚ) = radius

def chooseScale (w v : Fin k ⊕ Fin m → ℚ)
    (hw : ∀ j, 0 < w j) (hv : ∀ j, 0 < v j) : Scale w v := by
  let E : Fin (k + m) ≃ Fin k ⊕ Fin m := finSumFinEquiv.symm
  let s := WeightedGeometryScale.chooseScale (fun i => w (E i)) (fun i => v (E i))
    (fun i => hw (E i)) (fun i => hv (E i))
  refine ⟨s.radius, s.radius_pos, fun j => s.degreePowers (E.symm j),
    fun j => s.jetPowers (E.symm j), fun j => s.degreePowers_pos (E.symm j),
    fun j => s.jetPowers_pos (E.symm j), ?_, ?_⟩
  · intro j
    simpa only [Equiv.apply_symm_apply] using s.degreePowers_eq (E.symm j)
  · intro j
    simpa only [Equiv.apply_symm_apply] using s.jetPowers_eq (E.symm j)

def logCutoff (v : Fin k ⊕ Fin m → ℚ) : Fin m → Fin k → ℕ :=
  fun i r => (exists_nat_gt (v (Sum.inr i) / v (Sum.inl r))).choose

theorem logCutoff_strict (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j)
    (i : Fin m) (r : Fin k) :
    v (Sum.inr i) < (logCutoff v i r : ℚ) * v (Sum.inl r) :=
  (div_lt_iff₀ (hv (Sum.inl r))).mp
    (exists_nat_gt (v (Sum.inr i) / v (Sum.inl r))).choose_spec

namespace Scale

variable {w v : Fin k ⊕ Fin m → ℚ} (s : Scale w v)

abbrev Index (_s : Scale w v) := Unit ⊕ ((Fin k ⊕ Fin m) ⊕ (Fin k ⊕ Fin m))

def exponents : s.Index → (Fin k ⊕ Fin m) →₀ ℕ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun j => Finsupp.single j 1)
    (fun j => Finsupp.single j (s.degreePowers j)))

def constantIndex : s.Index := Sum.inl ()
def coordinateIndex (j : Fin k ⊕ Fin m) : s.Index := Sum.inr (Sum.inl j)
def pureIndex (j : Fin k ⊕ Fin m) : s.Index := Sum.inr (Sum.inr j)

@[simp] theorem exponents_constant : s.exponents s.constantIndex = 0 := rfl
@[simp] theorem exponents_coordinate (j : Fin k ⊕ Fin m) :
    s.exponents (s.coordinateIndex j) = Finsupp.single j 1 := rfl
@[simp] theorem exponents_pure (j : Fin k ⊕ Fin m) :
    s.exponents (s.pureIndex j) = Finsupp.single j (s.degreePowers j) := rfl

theorem coordinate_le_radius (hw : ∀ j, 0 < w j) (j : Fin k ⊕ Fin m) :
    w j ≤ s.radius := by
  have he : (1 : ℚ) ≤ s.degreePowers j := by exact_mod_cast s.degreePowers_pos j
  have h := mul_le_mul_of_nonneg_left he (hw j).le
  simpa only [mul_one, s.degreePowers_eq] using h

theorem budget (hw : ∀ j, 0 < w j) (b : s.Index) :
    Finsupp.weight w (s.exponents b) ≤ s.radius := by
  rcases b with u | (j | j)
  · simpa [exponents] using (show (0 : ℚ) ≤ s.radius by positivity)
  · simpa [exponents, Finsupp.weight_single] using s.coordinate_le_radius hw j
  · simpa [exponents, Finsupp.weight_single, nsmul_eq_mul, mul_comm] using
      (s.degreePowers_eq j).le

theorem budget_real (hw : ∀ j, 0 < w j) (b : s.Index) :
    Finsupp.weight (fun j => (w j : ℝ)) (s.exponents b) ≤ (s.radius : ℝ) := by
  have hq : (∑ j, w j * (s.exponents b j : ℚ)) ≤ (s.radius : ℚ) := by
    simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using s.budget hw b
  have hr : (∑ j, (w j : ℝ) * (s.exponents b j : ℝ)) ≤ (s.radius : ℝ) := by
    exact_mod_cast hq
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hr

abbrev compactification : Scheme := Proj (WeightedCompactification.imageGrade (R := ℂ) s.exponents)

def compactificationStructureMap : s.compactification ⟶ Spec (.of ℂ) :=
  WeightedCompactification.projection s.exponents

instance compactificationStructureMap_proper : IsProper s.compactificationStructureMap := by
  dsimp [compactificationStructureMap]
  infer_instance

def affineChart : affineSpace k m ⟶ s.compactification :=
  WeightedCompactification.affineChartMap s.exponents s.constantIndex s.exponents_constant
    s.coordinateIndex s.exponents_coordinate

instance affineChart_isOpenImmersion : IsOpenImmersion s.affineChart := by
  dsimp [affineChart]
  infer_instance

instance compactification_nonempty : Nonempty s.compactification :=
  ⟨s.affineChart ⟨WeightedBezout.pointIdeal (0 : Fin k ⊕ Fin m → ℂ), inferInstance⟩⟩

instance compactification_isIntegral : IsIntegral s.compactification := by infer_instance
instance compactification_isLocallyNoetherian : IsLocallyNoetherian s.compactification :=
  LocallyOfFiniteType.isLocallyNoetherian s.compactificationStructureMap
instance compactification_compact : CompactSpace s.compactification :=
  QuasiCompact.compactSpace_of_compactSpace s.compactificationStructureMap
instance compactification_isNoetherian : IsNoetherian s.compactification := {}
instance affineChart_quasiCompact : QuasiCompact s.affineChart := by infer_instance

theorem affineChart_over : s.affineChart ≫ s.compactificationStructureMap = structureMap k m :=
  CurveMonomialMap.affineChartMap_projection s.exponents s.constantIndex s.exponents_constant
    s.coordinateIndex s.exponents_coordinate

def hyperplane : LineBundle s.compactification := WeightedCompactification.lineBundle s.exponents

theorem hyperplane_ample : s.hyperplane.IsAmple :=
  WeightedCompactification.lineBundle_ample s.exponents

theorem hyperplane_eventual_supportBound (hw : ∀ j, 0 < w j) :
    ProjectiveCoefficientBound.EventualBound s.affineChart s.hyperplane
      (fun j => (w j : ℝ)) (s.radius : ℝ) :=
  WeightedGlobalSectionBound.eventual_supportBound s.exponents s.constantIndex
    s.exponents_constant s.coordinateIndex s.exponents_coordinate
    (fun j => (w j : ℝ)) (s.radius : ℝ) (s.budget_real hw)

def centerIdeal {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ) :
    s.compactification.IdealSheafData :=
  compactIdeal a c (logCutoff v) s.jetPowers s.affineChart

theorem centerIdeal_restrict {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ) :
    (s.centerIdeal a c).comap s.affineChart = affineIdeal a c (logCutoff v) s.jetPowers :=
  restrict_compactIdeal a c (logCutoff v) s.jetPowers s.affineChart

theorem centerIdeal_support {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hcY : ∀ b r, c b (Sum.inl r) ≠ 0) :
    ((s.centerIdeal a c).support : Set s.compactification) =
      ⋃ b, Set.range (point (c b) ≫ s.affineChart) :=
  support_compactIdeal a c hcY (logCutoff v) s.jetPowers s.jetPowers_pos s.affineChart
    s.compactificationStructureMap s.affineChart_over

theorem centerIdeal_support_finite {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hcY : ∀ b r, c b (Sum.inl r) ≠ 0) :
    ((s.centerIdeal a c).support : Set s.compactification).Finite := by
  rw [s.centerIdeal_support a c hcY]
  exact Set.finite_iUnion (fun _ => Set.finite_range _)

theorem centerIdeal_support_subset_chart {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hcY : ∀ b r, c b (Sum.inl r) ≠ 0) :
    ((s.centerIdeal a c).support : Set s.compactification) ⊆ s.affineChart.opensRange := by
  rw [s.centerIdeal_support a c hcY]
  intro x hx
  obtain ⟨b, z, rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨point (c b) z, rfl⟩

theorem centerIdeal_coherent {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ) :
    (LogExponentSeshadri.IdealModule.closedModule (s.centerIdeal a c)).IsFinitePresentation :=
  compactIdeal_isFinitePresentation a c (logCutoff v) s.jetPowers s.affineChart

/-- All affine-support, frame and degree-bound inputs are discharged for the
selected compactification; eventual geometric jet generation is still explicit. -/
theorem eventual_weighted_packets {J : Type} [Fintype J]
    (hw : ∀ j, 0 < w j) (hv : ∀ j, 0 < v j)
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (hc : Function.Injective c) (hcY : ∀ b r, c b (Sum.inl r) ≠ 0)
    (hjet : ∀ᶠ n : ℕ in atTop, Function.Surjective
      (BlowupJetSurjectivity.jetRestriction (s.centerIdeal a c) s.hyperplane n)) :
    ∀ᶠ n : ℕ in atTop,
      Function.Surjective (fun P : {P : MvPolynomial (Fin k ⊕ Fin m) ℂ //
          WeightedSliceDegree.SupportBound (fun j => (w j : ℝ))
            ((n : ℝ) * s.radius) P} => fun b =>
        JetGeometry.rationalCoefficientPacket v (n * s.radius)
          (MultivariateFormalJet.formalJet a (c b) P.val)) := by
  exact MultivariateAffineJetFramedPackets.eventual_weighted_packets_of_eventual_jetRestriction
    a c hc hcY (logCutoff v) s.jetPowers s.jetPowers_pos v hv
    (fun i r => (logCutoff_strict v hv i r).le) (s.radius : ℚ)
    (fun j => by rw [mul_comm, s.jetPowers_eq])
    s.affineChart (s.centerIdeal a c) s.hyperplane
    (AdmissibleMatrixInterpolation.monomialFrame_exists (R := ℂ) s.exponents
      s.constantIndex s.exponents_constant s.coordinateIndex s.exponents_coordinate)
    (s.centerIdeal_restrict a c) (s.centerIdeal_support_subset_chart a c hcY)
    (fun j => (w j : ℝ)) (s.radius : ℝ) (s.hyperplane_eventual_supportBound hw) hjet

end Scale
end
end GeneralizedLogarithms.MultivariateGeometryScale

/-- info: 'GeneralizedLogarithms.MultivariateGeometryScale.chooseScale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateGeometryScale.chooseScale

/-- info: 'GeneralizedLogarithms.MultivariateGeometryScale.Scale.hyperplane_ample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateGeometryScale.Scale.hyperplane_ample

/-- info: 'GeneralizedLogarithms.MultivariateGeometryScale.Scale.centerIdeal_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateGeometryScale.Scale.centerIdeal_support

/-- info: 'GeneralizedLogarithms.MultivariateGeometryScale.Scale.eventual_weighted_packets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateGeometryScale.Scale.eventual_weighted_packets
