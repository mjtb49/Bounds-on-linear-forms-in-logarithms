import GeneralizedLogarithms.MultivariateGeometricInterpolation
import GeneralizedLogarithms.MultivariateRationalJet

/-!
# A rational multilogarithmic interpolation matrix

Columns are all monomials in the weighted degree simplex. Rows are the actual
low formal-jet coefficients at the center family. Geometric interpolation gives
full row rank over the complex numbers; coefficient extension then produces a
nonzero full-row minor of the matrix defined over the rationals.
-/

namespace GeneralizedLogarithms.MultivariateInterpolationMatrix

noncomputable section
open scoped BigOperators
open Filter
open LogIrrationalityMeasure.LogExponent
open MultivariateAuxiliaryPolynomial

variable {k m : ℕ} {J : Type} [Fintype J]

theorem simplexExponent_inverse (d : (Fin k ⊕ Fin m) →₀ ℕ) :
    simplexExponent (fun i => d (indexEquiv i)) = d := by
  ext j
  simp

theorem weight_simplexExponent (w : Fin k ⊕ Fin m → ℝ) (d : Fin (k + m) → ℕ) :
    Finsupp.weight w (simplexExponent d) =
      ∑ i, w (indexEquiv i) * (d i : ℝ) := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul]
  rw [← indexEquiv.sum_comp (fun j => (simplexExponent d j : ℝ) * w j)]
  simp only [simplexExponent_apply, Equiv.symm_apply_apply, mul_comm]

def columnExponents (w : Fin k ⊕ Fin m → ℝ) (H : ℝ) :
    Finset ((Fin k ⊕ Fin m) →₀ ℕ) :=
  (realWeightedSimplex (fun i => w (indexEquiv i)) H).image simplexExponent

def jetExponents (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) :
    Finset ((Fin k ⊕ Fin m) →₀ ℕ) :=
  (strictWeightedSimplex (fun i => (v (indexEquiv i) : ℝ)) H).image simplexExponent

theorem mem_columnExponents (w : Fin k ⊕ Fin m → ℝ) (hw : ∀ j, 0 < w j)
    (H : ℝ) (d : (Fin k ⊕ Fin m) →₀ ℕ) :
    d ∈ columnExponents w H ↔ Finsupp.weight w d ≤ H := by
  classical
  constructor
  · intro h
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
    rw [weight_simplexExponent]
    exact (mem_realWeightedSimplex (fun i => hw (indexEquiv i))).mp hb
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨fun i => d (indexEquiv i), ?_, simplexExponent_inverse d⟩
    apply (mem_realWeightedSimplex (fun i => hw (indexEquiv i))).mpr
    simpa only [← weight_simplexExponent, simplexExponent_inverse] using h

theorem mem_jetExponents (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j)
    (H : ℚ) (d : (Fin k ⊕ Fin m) →₀ ℕ) :
    d ∈ jetExponents v H ↔ Finsupp.weight v d < H := by
  classical
  have hcast : (Finsupp.weight v d : ℝ) = Finsupp.weight (fun j => (v j : ℝ)) d := by
    simp [Finsupp.weight_eq_sum, nsmul_eq_mul]
  constructor
  · intro h
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp h
    have hh := (mem_strictWeightedSimplex (fun i => by exact_mod_cast hv (indexEquiv i))).mp hb
    rw [← weight_simplexExponent (fun j => (v j : ℝ)) b, he, ← hcast] at hh
    exact_mod_cast hh
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨fun i => d (indexEquiv i), ?_, simplexExponent_inverse d⟩
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hv (indexEquiv i))).mpr
    rw [← weight_simplexExponent (fun j => (v j : ℝ)) (fun i => d (indexEquiv i)),
      simplexExponent_inverse, ← hcast]
    exact_mod_cast h

abbrev Column (w : Fin k ⊕ Fin m → ℝ) (H : ℝ) := ↥(columnExponents w H)
abbrev Row (J : Type) (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) := J × ↥(jetExponents v H)

theorem weighted_expansion (w : Fin k ⊕ Fin m → ℝ) (hw : ∀ j, 0 < w j)
    (H : ℝ) (P : MvPolynomial (Fin k ⊕ Fin m) ℂ)
    (hP : WeightedSliceDegree.SupportBound w H P) :
    ∑ e : Column w H, MvPolynomial.monomial e.val (P.coeff e.val) = P := by
  classical
  calc
    _ = ∑ e ∈ columnExponents w H, MvPolynomial.monomial e (P.coeff e) :=
      Finset.sum_coe_sort _ _
    _ = ∑ e ∈ P.support, MvPolynomial.monomial e (P.coeff e) := by
      symm
      apply Finset.sum_subset (fun d hd => (mem_columnExponents w hw H d).mpr (hP d hd))
      intro d hd hnot
      have hz : P.coeff d = 0 := by
        by_contra h
        exact hnot (MvPolynomial.mem_support_iff.mpr h)
      simp [hz]
    _ = P := MvPolynomial.support_sum_monomial_coeff P

def complexMatrix (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℂ)
    (w : Fin k ⊕ Fin m → ℝ) (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) :
    Matrix (Row J v H) (Column w H) ℂ := fun ρ e =>
  MvPowerSeries.coeff ρ.2.val
    (MultivariateFormalJet.formalJet a (c ρ.1) (MvPolynomial.monomial e.val 1))

def rationalMatrix (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℚ)
    (w : Fin k ⊕ Fin m → ℝ) (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) :
    Matrix (Row J v H) (Column w H) ℚ := fun ρ e =>
  MvPowerSeries.coeff ρ.2.val
    (MultivariateRationalJet.formalJet a (c ρ.1) (MvPolynomial.monomial e.val 1))

omit [Fintype J] in
theorem matrix_cast (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℚ)
    (w : Fin k ⊕ Fin m → ℝ) (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) :
    (rationalMatrix a c w v H).map (algebraMap ℚ ℂ) =
      complexMatrix a (fun b j => (c b j : ℂ)) w v H := by
  ext ρ e
  have h := MultivariateRationalJet.cast_coeff_formalJet a (c ρ.1)
    (MvPolynomial.monomial e.val 1) ρ.2.val
  simpa [rationalMatrix, complexMatrix] using h

omit [Fintype J] in
theorem mulVec_coefficients (a : Fin m → Fin k → ℤ)
    (c : J → Fin k ⊕ Fin m → ℂ) (w : Fin k ⊕ Fin m → ℝ)
    (hw : ∀ j, 0 < w j) (v : Fin k ⊕ Fin m → ℚ) (H : ℚ)
    (P : MvPolynomial (Fin k ⊕ Fin m) ℂ) (hP : WeightedSliceDegree.SupportBound w H P)
    (ρ : Row J v H) :
    (complexMatrix a c w v H).mulVecLin (fun e => P.coeff e.val) ρ =
      MvPowerSeries.coeff ρ.2.val (MultivariateFormalJet.formalJet a (c ρ.1) P) := by
  classical
  conv_rhs => rw [← weighted_expansion w hw H P hP]
  simp only [map_sum]
  change (∑ e : Column w H, _ * _) = _
  apply Finset.sum_congr rfl
  intro e he
  have hmon : MvPolynomial.monomial e.val (P.coeff e.val) =
      P.coeff e.val • (MvPolynomial.monomial e.val 1 : MvPolynomial (Fin k ⊕ Fin m) ℂ) := by
    simp [MvPolynomial.smul_monomial]
  rw [hmon, map_smul, map_smul]
  exact mul_comm _ _

omit [Fintype J] in
theorem surjective_of_packets (a : Fin m → Fin k → ℤ)
    (c : J → Fin k ⊕ Fin m → ℂ) (w : Fin k ⊕ Fin m → ℝ)
    (hw : ∀ j, 0 < w j) (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ)
    (hpacket : Function.Surjective (fun P : {P : MvPolynomial (Fin k ⊕ Fin m) ℂ //
        WeightedSliceDegree.SupportBound w H P} => fun b =>
      JetGeometry.rationalCoefficientPacket v H (MultivariateFormalJet.formalJet a (c b) P.val))) :
    Function.Surjective (complexMatrix a c w v H).mulVecLin := by
  intro y
  let packet : J → JetGeometry.RationalCoefficientPacket (R := ℂ) v H := fun b d =>
    y (b, ⟨d.val, (mem_jetExponents v hv H d.val).mpr d.property⟩)
  obtain ⟨P, hP⟩ := hpacket packet
  refine ⟨fun e => P.val.coeff e.val, ?_⟩
  funext ρ
  rw [mulVec_coefficients a c w hw v H P.val P.property]
  exact congrFun (congrFun hP ρ.1)
    ⟨ρ.2.val, (mem_jetExponents v hv H ρ.2.val).mp ρ.2.property⟩

variable [DecidableEq J]

/-- A nonzero rational full-row minor, derived from actual complex jet packets. -/
theorem rational_minor_of_packets (a : Fin m → Fin k → ℤ)
    (c : J → Fin k ⊕ Fin m → ℚ) (w : Fin k ⊕ Fin m → ℝ)
    (hw : ∀ j, 0 < w j) (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ)
    (hpacket : Function.Surjective (fun P : {P : MvPolynomial (Fin k ⊕ Fin m) ℂ //
        WeightedSliceDegree.SupportBound w H P} => fun b =>
      JetGeometry.rationalCoefficientPacket v H
        (MultivariateFormalJet.formalJet a (fun j => (c b j : ℂ)) P.val))) :
    ∃ selection : Row J v H → Column w H, Function.Injective selection ∧
      ((rationalMatrix a c w v H).submatrix id selection).det ≠ 0 := by
  classical
  obtain ⟨s, hs, hdet⟩ := InterpolationMatrix.exists_full_row_minor_of_surjective
    (complexMatrix a (fun b j => (c b j : ℂ)) w v H)
    (surjective_of_packets a _ w hw v hv H hpacket)
  refine ⟨s, hs, ?_⟩
  intro hz
  apply hdet
  rw [← matrix_cast]
  change (((rationalMatrix a c w v H).submatrix id s).map (algebraMap ℚ ℂ)).det = 0
  simpa only [hz, map_zero, RingHom.mapMatrix_apply] using
    ((algebraMap ℚ ℂ).map_det ((rationalMatrix a c w v H).submatrix id s)).symm

variable [LinearOrder (Fin k ⊕ Fin m)]

/-- The numerical curve hypotheses now yield actual rational nonzero minors
at every sufficiently large multiple of a common positive integer scale. -/
theorem eventual_rational_minor (hk : 0 < k)
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℚ)
    (d : MultivariateCurveMargin.NumericalData a (fun b j => (c b j : ℂ))) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
      ∃ selection : Row J d.v (n * R) → Column (fun j => (d.w j : ℝ)) (((n : ℚ) * (R : ℚ) : ℚ) : ℝ),
        Function.Injective selection ∧
          ((rationalMatrix a c (fun j => (d.w j : ℝ)) d.v (n * R)).submatrix id selection).det ≠ 0 := by
  obtain ⟨R, hR, h⟩ := MultivariateGeometricInterpolation.eventual_weighted_packets hk d
  refine ⟨R, hR, ?_⟩
  filter_upwards [h] with n hn
  apply rational_minor_of_packets a c (fun j => (d.w j : ℝ))
    (fun j => by exact_mod_cast d.w_pos j) d.v d.v_pos (n * R)
  intro packet
  obtain ⟨P, hP⟩ := hn packet
  refine ⟨⟨P.val, ?_⟩, hP⟩
  simpa only [Rat.cast_mul, Rat.cast_natCast] using P.property

end
end GeneralizedLogarithms.MultivariateInterpolationMatrix

/-- info: 'GeneralizedLogarithms.MultivariateInterpolationMatrix.matrix_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateInterpolationMatrix.matrix_cast

/-- info: 'GeneralizedLogarithms.MultivariateInterpolationMatrix.rational_minor_of_packets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateInterpolationMatrix.rational_minor_of_packets

/-- info: 'GeneralizedLogarithms.MultivariateInterpolationMatrix.eventual_rational_minor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateInterpolationMatrix.eventual_rational_minor
