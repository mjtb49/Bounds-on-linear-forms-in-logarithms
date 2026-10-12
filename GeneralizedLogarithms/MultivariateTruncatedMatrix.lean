import GeneralizedLogarithms.MultivariateInterpolationMatrix

/-!
# Nonzero rational minors for fixed logarithm truncations

The arithmetic matrix uses polynomial logarithm truncations whose degrees are
fixed before the height tends to infinity. The weighted coordinate change
transfers full-log interpolation to these truncated jets at every height.
Their entries are rational, and a nonzero full-row minor follows along the
same cofinal integral scale. Denominator size estimates remain separate.
-/

namespace GeneralizedLogarithms.MultivariateTruncatedMatrix

noncomputable section
open scoped BigOperators
open Filter MvPowerSeries
open LogIrrationalityMeasure.LogExponent
open MultivariateInterpolationMatrix

variable {k m : ℕ} {J : Type}

def coordinates (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℚ)
    (T : Fin m → Fin k → ℕ) : (Fin k ⊕ Fin m) → MvPowerSeries (Fin k ⊕ Fin m) ℚ :=
  Sum.elim (fun r => C (c (Sum.inl r)) * (1 + X (Sum.inl r)))
    (fun i => C (c (Sum.inr i)) + X (Sum.inr i) + ∑ r, C (a i r : ℚ) *
      (PowerSeries.trunc (T i r) (PowerSeries.log ℚ) : PowerSeries ℚ).toMvPowerSeries (Sum.inl r))

def rationalJet (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℚ)
    (T : Fin m → Fin k → ℕ) :
    MvPolynomial (Fin k ⊕ Fin m) ℚ →ₐ[ℚ] MvPowerSeries (Fin k ⊕ Fin m) ℚ :=
  MvPolynomial.aeval (coordinates a c T)

theorem map_truncatedLog (T : ℕ) :
    PowerSeries.map (algebraMap ℚ ℂ) (PowerSeries.trunc T (PowerSeries.log ℚ) : PowerSeries ℚ) =
      (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) := by
  ext n
  simp [PowerSeries.coeff_map, PowerSeries.coeff_trunc, PowerSeries.coeff_log]
  split_ifs <;> push_cast <;> rfl

theorem map_coordinates (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℚ)
    (T : Fin m → Fin k → ℕ) (j : Fin k ⊕ Fin m) :
    MvPowerSeries.map (algebraMap ℚ ℂ) (coordinates a c T j) =
      MultivariateLogPolynomialAdapter.truncatedFormalJet a (fun j => (c j : ℂ)) T
        (MvPolynomial.X j) := by
  cases j with
  | inl r => simp [coordinates, MultivariateFormalLogShift.truncatedFormalJet_Y]
  | inr i =>
    simp [coordinates, MultivariateFormalLogShift.truncatedFormalJet_X,
      MultivariateRationalJet.map_lift, map_truncatedLog]

theorem map_rationalJet (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℚ)
    (T : Fin m → Fin k → ℕ) (P : MvPolynomial (Fin k ⊕ Fin m) ℚ) :
    MvPowerSeries.map (algebraMap ℚ ℂ) (rationalJet a c T P) =
      MultivariateLogPolynomialAdapter.truncatedFormalJet a (fun j => (c j : ℂ)) T
        (MvPolynomial.map (algebraMap ℚ ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C q =>
    simp [rationalJet, MultivariateLogPolynomialAdapter.truncatedFormalJet,
      MvPowerSeries.algebraMap_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    simp only [map_mul, hP, MvPolynomial.map_X]
    congr 1
    simpa only [rationalJet, MvPolynomial.aeval_X] using map_coordinates a c T j

/-- The matrix of any family of linear jet substitutions on the whole degree simplex. -/
def packetMatrix (F : J → MvPolynomial (Fin k ⊕ Fin m) ℂ →ₐ[ℂ]
    MvPowerSeries (Fin k ⊕ Fin m) ℂ) (w : Fin k ⊕ Fin m → ℝ)
    (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) : Matrix (Row J v H) (Column w H) ℂ :=
  fun ρ e => coeff ρ.2.val (F ρ.1 (MvPolynomial.monomial e.val 1))

theorem packetMatrix_mulVec (F : J → MvPolynomial (Fin k ⊕ Fin m) ℂ →ₐ[ℂ]
    MvPowerSeries (Fin k ⊕ Fin m) ℂ) (w : Fin k ⊕ Fin m → ℝ)
    (hw : ∀ j, 0 < w j) (v : Fin k ⊕ Fin m → ℚ) (H : ℚ)
    (P : MvPolynomial (Fin k ⊕ Fin m) ℂ) (hP : WeightedSliceDegree.SupportBound w H P)
    (ρ : Row J v H) :
    (packetMatrix F w v H).mulVecLin (fun e => P.coeff e.val) ρ = coeff ρ.2.val (F ρ.1 P) := by
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

theorem packetMatrix_surjective (F : J → MvPolynomial (Fin k ⊕ Fin m) ℂ →ₐ[ℂ]
    MvPowerSeries (Fin k ⊕ Fin m) ℂ) (w : Fin k ⊕ Fin m → ℝ)
    (hw : ∀ j, 0 < w j) (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ)
    (hpacket : Function.Surjective (fun P : {P : MvPolynomial (Fin k ⊕ Fin m) ℂ //
        WeightedSliceDegree.SupportBound w H P} => fun b =>
      JetGeometry.rationalCoefficientPacket v H (F b P.val))) :
    Function.Surjective (packetMatrix F w v H).mulVecLin := by
  intro y
  let packet : J → JetGeometry.RationalCoefficientPacket (R := ℂ) v H := fun b d =>
    y (b, ⟨d.val, (mem_jetExponents v hv H d.val).mpr d.property⟩)
  obtain ⟨P, hP⟩ := hpacket packet
  refine ⟨fun e => P.val.coeff e.val, ?_⟩
  funext ρ
  rw [packetMatrix_mulVec F w hw v H P.val P.property]
  exact congrFun (congrFun hP ρ.1)
    ⟨ρ.2.val, (mem_jetExponents v hv H ρ.2.val).mp ρ.2.property⟩

def matrix (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℚ)
    (T : Fin m → Fin k → ℕ) (w : Fin k ⊕ Fin m → ℝ)
    (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) : Matrix (Row J v H) (Column w H) ℚ :=
  fun ρ e => coeff ρ.2.val (rationalJet a (c ρ.1) T (MvPolynomial.monomial e.val 1))

theorem matrix_cast (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℚ)
    (T : Fin m → Fin k → ℕ) (w : Fin k ⊕ Fin m → ℝ) (v : Fin k ⊕ Fin m → ℚ) (H : ℚ) :
    (matrix a c T w v H).map (algebraMap ℚ ℂ) =
      packetMatrix (fun b => MultivariateLogPolynomialAdapter.truncatedFormalJet a
        (fun j => (c b j : ℂ)) T) w v H := by
  ext ρ e
  have h := congrArg (coeff ρ.2.val) (map_rationalJet a (c ρ.1) T (MvPolynomial.monomial e.val 1))
  simpa [matrix, packetMatrix, MvPowerSeries.coeff_map] using h

variable [Fintype J] [DecidableEq J]

theorem rational_minor_of_full_packets (a : Fin m → Fin k → ℤ)
    (c : J → Fin k ⊕ Fin m → ℚ) (T : Fin m → Fin k → ℕ)
    (w : Fin k ⊕ Fin m → ℝ) (hw : ∀ j, 0 < w j)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r))
    (hpacket : Function.Surjective (fun P : {P : MvPolynomial (Fin k ⊕ Fin m) ℂ //
        WeightedSliceDegree.SupportBound w H P} => fun b =>
      JetGeometry.rationalCoefficientPacket v H
        (MultivariateFormalJet.formalJet a (fun j => (c b j : ℂ)) P.val))) :
    ∃ selection : Row J v H → Column w H, Function.Injective selection ∧
      ((matrix a c T w v H).submatrix id selection).det ≠ 0 := by
  classical
  have htrunc := (MultivariateFormalLogShift.formalLog_packets_surjective_iff_truncated
    a v (fun j => (hv j).le) H T hT (fun b j => (c b j : ℂ))
    (fun P : {P : MvPolynomial (Fin k ⊕ Fin m) ℂ // WeightedSliceDegree.SupportBound w H P} =>
      P.val)).mp hpacket
  obtain ⟨s, hs, hdet⟩ := InterpolationMatrix.exists_full_row_minor_of_surjective
    (packetMatrix (fun b => MultivariateLogPolynomialAdapter.truncatedFormalJet a
      (fun j => (c b j : ℂ)) T) w v H)
    (packetMatrix_surjective _ w hw v hv H htrunc)
  refine ⟨s, hs, ?_⟩
  intro hz
  apply hdet
  rw [← matrix_cast]
  change (((matrix a c T w v H).submatrix id s).map (algebraMap ℚ ℂ)).det = 0
  simpa only [hz, map_zero, RingHom.mapMatrix_apply] using
    ((algebraMap ℚ ℂ).map_det ((matrix a c T w v H).submatrix id s)).symm

variable [LinearOrder (Fin k ⊕ Fin m)]

/-- The cutoff matrix is fixed before `n` varies. Neither rationality of entries,
full row rank, nor existence of a nonzero minor is assumed. -/
theorem eventual_rational_minor (hk : 0 < k)
    (a : Fin m → Fin k → ℤ) (c : J → Fin k ⊕ Fin m → ℚ)
    (d : MultivariateCurveMargin.NumericalData a (fun b j => (c b j : ℂ)))
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, d.v (Sum.inr i) ≤ (T i r : ℚ) * d.v (Sum.inl r)) :
    ∃ R : ℕ, 0 < R ∧ ∀ᶠ n : ℕ in atTop,
      ∃ selection : Row J d.v (n * R) →
          Column (fun j => (d.w j : ℝ)) (((n : ℚ) * (R : ℚ) : ℚ) : ℝ),
        Function.Injective selection ∧
          ((matrix a c T (fun j => (d.w j : ℝ)) d.v (n * R)).submatrix id selection).det ≠ 0 := by
  obtain ⟨R, hR, h⟩ := MultivariateGeometricInterpolation.eventual_weighted_packets hk d
  refine ⟨R, hR, ?_⟩
  filter_upwards [h] with n hn
  apply rational_minor_of_full_packets a c T (fun j => (d.w j : ℝ))
    (fun j => by exact_mod_cast d.w_pos j) d.v d.v_pos (n * R) hT
  intro packet
  obtain ⟨P, hP⟩ := hn packet
  refine ⟨⟨P.val, ?_⟩, hP⟩
  simpa only [Rat.cast_mul, Rat.cast_natCast] using P.property

end
end GeneralizedLogarithms.MultivariateTruncatedMatrix

/-- info: 'GeneralizedLogarithms.MultivariateTruncatedMatrix.map_rationalJet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateTruncatedMatrix.map_rationalJet

/-- info: 'GeneralizedLogarithms.MultivariateTruncatedMatrix.rational_minor_of_full_packets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateTruncatedMatrix.rational_minor_of_full_packets

/-- info: 'GeneralizedLogarithms.MultivariateTruncatedMatrix.eventual_rational_minor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateTruncatedMatrix.eventual_rational_minor
