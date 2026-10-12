import LogIrrationalityMeasure.Jets.FormalBranchEvaluation
import LogIrrationalityMeasure.Jets.OrdinaryDVRBranchJet
import LogIrrationalityMeasure.Geometry.PlaceCenteredBranch

/-!
# Branch coordinates with several logarithms

At a center `(cY,cX)`, use `t_r = Y_r/cY_r - 1` and
`u_i = X_i - cX_i - ∑ r, a_i_r log(1+t_r)`. These are genuine formal power
series. Their constant longitudinal specialization has zero longitudinal
coordinates and exactly the ordinary transverse branch coordinates.

This file proves coordinate and contact identities. It does not assert a
multivariate derivative-word order estimate or formal-jet vanishing theorem.
-/

namespace GeneralizedLogarithms.MultilogBranchCoordinates

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent

variable {k m : ℕ}

def centeredY (c : ℂ) (y : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C c⁻¹ * y - 1

theorem constantCoeff_centeredY (c : ℂ) (hc : c ≠ 0) (y : PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = c) :
    PowerSeries.constantCoeff (centeredY c y) = 0 := by
  simp [centeredY, hy, inv_mul_cancel₀ hc]

theorem centeredY_eq_zero_iff (c : ℂ) (hc : c ≠ 0) (y : PowerSeries ℂ) :
    centeredY c y = 0 ↔ y = PowerSeries.C c := by
  constructor
  · intro h
    have h1 : PowerSeries.C c⁻¹ * y = 1 := sub_eq_zero.mp h
    calc
      y = PowerSeries.C c * (PowerSeries.C c⁻¹ * y) := by
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
      _ = PowerSeries.C c := by rw [h1, mul_one]
  · intro h
    simp [centeredY, h, ← map_mul, inv_mul_cancel₀ hc]

/-- Formal branch coordinates, with all logarithms represented by substitution
in the formal series `log(1+T)`. -/
def branchCoordinates (a : Fin m → Fin k → ℤ) (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ) :
    (Fin k ⊕ Fin m) → PowerSeries ℂ :=
  Sum.elim (fun r => centeredY (cY r) (y r))
    (fun i => x i - PowerSeries.C (cX i) -
      ∑ r, PowerSeries.C (a i r : ℂ) *
        PowerSeries.subst (centeredY (cY r) (y r)) (PowerSeries.log ℂ))

theorem branchCoordinates_centered (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : ∀ r, PowerSeries.constantCoeff (y r) = cY r)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = cX i) :
    ∀ j, PowerSeries.constantCoeff (branchCoordinates a cY cX y x j) = 0 := by
  have ht (r : Fin k) : PowerSeries.constantCoeff (centeredY (cY r) (y r)) = 0 :=
    constantCoeff_centeredY (cY r) (hcY r) (y r) (hy r)
  have hlog (r : Fin k) : PowerSeries.constantCoeff
      (PowerSeries.subst (centeredY (cY r) (y r)) (PowerSeries.log ℂ)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (ht r) _ PowerSeries.constantCoeff_log
  intro j
  cases j with
  | inl r => exact ht r
  | inr i =>
      change PowerSeries.constantCoeff (x i - PowerSeries.C (cX i) -
        ∑ r, PowerSeries.C (a i r : ℂ) *
          PowerSeries.subst (centeredY (cY r) (y r)) (PowerSeries.log ℂ)) = 0
      simp only [map_sub, map_sum, map_mul, PowerSeries.constantCoeff_C, hx,
        hlog,
        mul_zero, Finset.sum_const_zero, sub_self, sub_zero]

theorem branchCoordinates_hasSubst (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : ∀ r, PowerSeries.constantCoeff (y r) = cY r)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = cX i) :
    MvPowerSeries.HasSubst (branchCoordinates a cY cX y x) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero
    (branchCoordinates_centered a cY cX hcY y x hy hx)

theorem branchCoordinates_constant_longitudinal (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (x : Fin m → PowerSeries ℂ) :
    branchCoordinates a cY cX (fun r => PowerSeries.C (cY r)) x =
      Sum.elim (fun _ : Fin k => 0) (OrdinaryAuxiliaryJet.branchCoordinates cX x) := by
  have ht (r : Fin k) : centeredY (cY r) (PowerSeries.C (cY r)) = 0 :=
    (centeredY_eq_zero_iff (cY r) (hcY r) _).mpr rfl
  funext j
  cases j <;> simp only [branchCoordinates, Sum.elim_inl, Sum.elim_inr, ht,
    PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log,
    mul_zero, Finset.sum_const_zero, sub_zero, OrdinaryAuxiliaryJet.branchCoordinates]

theorem branchCoordinates_nonzero (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hnc : (∃ r, y r ≠ PowerSeries.C (cY r)) ∨ ∃ i, x i ≠ PowerSeries.C (cX i)) :
    ∃ j, branchCoordinates a cY cX y x j ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hY : y = fun r => PowerSeries.C (cY r) := by
    funext r
    exact (centeredY_eq_zero_iff (cY r) (hcY r) _).mp (h (Sum.inl r))
  rcases hnc with ⟨r, hr⟩ | ⟨i, hi⟩
  · exact hr (congrFun hY r)
  · have hu := h (Sum.inr i)
    rw [hY, branchCoordinates_constant_longitudinal a cY cX hcY] at hu
    exact hi (sub_eq_zero.mp hu)

/-- Appending any finite block of zero coordinates does not change contact. -/
theorem contact_zero_sum (v : (Fin k ⊕ Fin m) → ℚ)
    (b : Fin m → PowerSeries ℂ) (hb : ∃ i, b i ≠ 0)
    (hfull : ∃ j, (Sum.elim (fun _ : Fin k => 0) b) j ≠ 0) :
    BranchContact.contact v (Sum.elim (fun _ : Fin k => 0) b) hfull =
      BranchContact.contact (fun i => v (Sum.inr i)) b hb := by
  apply le_antisymm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains (fun i => v (Sum.inr i)) b hb
    have hh := BranchContact.contact_le v (Sum.elim (fun _ : Fin k => 0) b) hfull
      (Sum.inr i) hi
    exact hh.trans_eq he.symm
  · obtain ⟨j, hj, he⟩ := BranchContact.exists_attains v
      (Sum.elim (fun _ : Fin k => 0) b) hfull
    cases j with
    | inl r => exact (hj rfl).elim
    | inr i =>
        exact (BranchContact.contact_le (fun i => v (Sum.inr i)) b hb i hj).trans_eq he.symm

section DVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

def coordinates (a : Fin m → Fin k → ℤ) (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (y : Fin k → A) (x : Fin m → A) : (Fin k ⊕ Fin m) → PowerSeries ℂ :=
  branchCoordinates a cY cX (fun r => DVRBranch.expansion ℂ A (y r))
    (fun i => DVRBranch.expansion ℂ A (x i))

theorem coordinates_centered (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → A) (x : Fin m → A)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (y r) = cY r)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = cX i) :
    ∀ j, PowerSeries.constantCoeff (coordinates a cY cX y x j) = 0 := by
  apply branchCoordinates_centered a cY cX hcY
  · intro r; simpa using hy r
  · intro i; simpa using hx i

theorem coordinates_nonzero (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → A) (x : Fin m → A)
    (hnc : (∃ r, y r ≠ algebraMap ℂ A (cY r)) ∨
      ∃ i, x i ≠ algebraMap ℂ A (cX i)) : ∃ j, coordinates a cY cX y x j ≠ 0 := by
  apply branchCoordinates_nonzero a cY cX hcY
  rcases hnc with ⟨r, hr⟩ | ⟨i, hi⟩
  · left
    refine ⟨r, fun hz => hr ?_⟩
    apply DVRBranch.expansion_injective ℂ A
    rw [AlgHom.commutes]
    exact hz
  · right
    refine ⟨i, fun hz => hi ?_⟩
    apply DVRBranch.expansion_injective ℂ A
    rw [AlgHom.commutes]
    exact hz

def contact (v : (Fin k ⊕ Fin m) → ℚ) (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → A) (x : Fin m → A)
    (hnc : (∃ r, y r ≠ algebraMap ℂ A (cY r)) ∨
      ∃ i, x i ≠ algebraMap ℂ A (cX i)) : ℚ :=
  BranchContact.contact v (coordinates a cY cX y x)
    (coordinates_nonzero a cY cX hcY y x hnc)

theorem contact_pos (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j)
    (a : Fin m → Fin k → ℤ) (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (hcY : ∀ r, cY r ≠ 0) (y : Fin k → A) (x : Fin m → A)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (y r) = cY r)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = cX i)
    (hnc : (∃ r, y r ≠ algebraMap ℂ A (cY r)) ∨
      ∃ i, x i ≠ algebraMap ℂ A (cX i)) :
    0 < contact v a cY cX hcY y x hnc :=
  BranchContact.contact_pos v hv _ _ (coordinates_centered a cY cX hcY y x hy hx)

theorem coordinates_constant_longitudinal (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0) (x : Fin m → A) :
    coordinates a cY cX (fun r => algebraMap ℂ A (cY r)) x =
      Sum.elim (fun _ : Fin k => 0) (OrdinaryDVRBranchJet.coordinates cX x) := by
  unfold coordinates
  simp only [AlgHom.commutes]
  exact branchCoordinates_constant_longitudinal a cY cX hcY _

theorem contact_constant_longitudinal (v : (Fin k ⊕ Fin m) → ℚ)
    (a : Fin m → Fin k → ℤ) (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (hcY : ∀ r, cY r ≠ 0) (x : Fin m → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (cX i)) :
    contact v a cY cX hcY (fun r => algebraMap ℂ A (cY r)) x (Or.inr hnc) =
      OrdinaryDVRBranchJet.contact (fun i => v (Sum.inr i)) cX x hnc := by
  have hb := OrdinaryDVRBranchJet.coordinates_nonzero cX x hnc
  have hfull : ∃ j, (Sum.elim (fun _ : Fin k => 0)
      (OrdinaryDVRBranchJet.coordinates cX x)) j ≠ 0 := by
    obtain ⟨i, hi⟩ := hb
    exact ⟨Sum.inr i, hi⟩
  have hcongr {b d : (Fin k ⊕ Fin m) → PowerSeries ℂ} (he : b = d)
      (hb : ∃ i, b i ≠ 0) (hd : ∃ i, d i ≠ 0) :
      BranchContact.contact v b hb = BranchContact.contact v d hd := by subst d; rfl
  exact (hcongr (coordinates_constant_longitudinal a cY cX hcY x)
    (coordinates_nonzero a cY cX hcY _ x (Or.inr hnc)) hfull).trans
    (contact_zero_sum v (OrdinaryDVRBranchJet.coordinates cX x) hb hfull)

end DVR

section Places

open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch

variable {E : Type*} [Field E] [Algebra ℂ E]

theorem transverse_nonconstant_of_constant_longitudinal
    (z : (Fin k ⊕ Fin m) → E) (c : (Fin k ⊕ Fin m) → ℂ)
    (hY : ∀ r, z (Sum.inl r) = algebraMap ℂ E (c (Sum.inl r)))
    (hnc : ∃ j, z j ≠ algebraMap ℂ E (c j)) :
    ∃ i, z (Sum.inr i) ≠ algebraMap ℂ E (c (Sum.inr i)) := by
  obtain ⟨j, hj⟩ := hnc
  cases j with
  | inl r => exact (hj (hY r)).elim
  | inr i => exact ⟨i, hj⟩

theorem lifted_nonconstant
    (p : NormalizedPlace ℂ E) (z : (Fin k ⊕ Fin m) → E) (c : (Fin k ⊕ Fin m) → ℂ)
    (hc : Centered z c p) (hnc : ∃ j, z j ≠ algebraMap ℂ E (c j)) :
    (∃ r, lift p z c hc (Sum.inl r) ≠ algebraMap ℂ (ring p) (c (Sum.inl r))) ∨
      ∃ i, lift p z c hc (Sum.inr i) ≠ algebraMap ℂ (ring p) (c (Sum.inr i)) := by
  obtain ⟨j, hj⟩ := lift_nonconstant p z c hc hnc
  cases j with
  | inl r => exact Or.inl ⟨r, hj⟩
  | inr i => exact Or.inr ⟨i, hj⟩

variable (p : NormalizedPlace ℂ E)
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

/-- Multilogarithmic contact at a normalized place, using its actual DVR expansion. -/
def placeContact (a : Fin m → Fin k → ℤ)
    (z : (Fin k ⊕ Fin m) → E) (c : (Fin k ⊕ Fin m) → ℂ)
    (hcY : ∀ r, c (Sum.inl r) ≠ 0) (hc : Centered z c p)
    (hnc : ∃ j, z j ≠ algebraMap ℂ E (c j)) (v : (Fin k ⊕ Fin m) → ℚ) : ℚ :=
  contact v a (fun r => c (Sum.inl r)) (fun i => c (Sum.inr i)) hcY
    (fun r => lift p z c hc (Sum.inl r)) (fun i => lift p z c hc (Sum.inr i))
    (lifted_nonconstant p z c hc hnc)

theorem placeContact_pos (a : Fin m → Fin k → ℤ)
    (z : (Fin k ⊕ Fin m) → E) (c : (Fin k ⊕ Fin m) → ℂ)
    (hcY : ∀ r, c (Sum.inl r) ≠ 0) (hc : Centered z c p)
    (hnc : ∃ j, z j ≠ algebraMap ℂ E (c j))
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j) :
    0 < placeContact p a z c hcY hc hnc v :=
  contact_pos v hv a _ _ hcY _ _ (fun r => lift_residue p z c hc (Sum.inl r))
    (fun i => lift_residue p z c hc (Sum.inr i)) _

/-- Constant longitudinal coordinates reduce the genuine multilogarithmic
place contact to the ordinary contact of the transverse coordinate family. -/
theorem placeContact_of_constant_longitudinal (a : Fin m → Fin k → ℤ)
    (z : (Fin k ⊕ Fin m) → E) (c : (Fin k ⊕ Fin m) → ℂ)
    (hcY : ∀ r, c (Sum.inl r) ≠ 0) (hc : Centered z c p)
    (hnc : ∃ j, z j ≠ algebraMap ℂ E (c j)) (v : (Fin k ⊕ Fin m) → ℚ)
    (hY : ∀ r, z (Sum.inl r) = algebraMap ℂ E (c (Sum.inl r))) :
    placeContact p a z c hcY hc hnc v =
      ordinaryContact p (fun i => z (Sum.inr i)) (fun i => c (Sum.inr i))
        (fun i => hc (Sum.inr i))
        (transverse_nonconstant_of_constant_longitudinal z c hY hnc)
        (fun i => v (Sum.inr i)) := by
  have hy : (fun r => lift p z c hc (Sum.inl r)) =
      fun r => algebraMap ℂ (ring p) (c (Sum.inl r)) := by
    funext r
    exact (lift_eq_algebraMap_iff p z c hc (Sum.inl r) (c (Sum.inl r))).mpr (hY r)
  have hx : (fun i => lift p z c hc (Sum.inr i)) =
      lift p (fun i => z (Sum.inr i)) (fun i => c (Sum.inr i)) (fun i => hc (Sum.inr i)) := rfl
  simpa only [placeContact, ordinaryContact, hy, hx] using
    contact_constant_longitudinal v a (fun r => c (Sum.inl r)) (fun i => c (Sum.inr i)) hcY
      (lift p (fun i => z (Sum.inr i)) (fun i => c (Sum.inr i)) (fun i => hc (Sum.inr i)))
      (lift_nonconstant p _ _ _
        (transverse_nonconstant_of_constant_longitudinal z c hY hnc))

end Places

end
end GeneralizedLogarithms.MultilogBranchCoordinates

/-- info: 'GeneralizedLogarithms.MultilogBranchCoordinates.branchCoordinates_hasSubst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultilogBranchCoordinates.branchCoordinates_hasSubst

/-- info: 'GeneralizedLogarithms.MultilogBranchCoordinates.branchCoordinates_constant_longitudinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultilogBranchCoordinates.branchCoordinates_constant_longitudinal

/-- info: 'GeneralizedLogarithms.MultilogBranchCoordinates.contact_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultilogBranchCoordinates.contact_pos

/-- info: 'GeneralizedLogarithms.MultilogBranchCoordinates.contact_constant_longitudinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultilogBranchCoordinates.contact_constant_longitudinal

/-- info: 'GeneralizedLogarithms.MultilogBranchCoordinates.placeContact_of_constant_longitudinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultilogBranchCoordinates.placeContact_of_constant_longitudinal
