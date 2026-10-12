import GeneralizedLogarithms.MultivariateLogTruncation
import LogIrrationalityMeasure.Analysis.LogarithmicContactIdeal

/-!
# Local ideals for truncated multilogarithmic coordinates

The generators are powers of the normalized longitudinal coordinates and of
the transverse coordinates corrected by finite sums of truncated logarithms.
Under the explicit strict truncation bounds, their DVR colength is exactly
the common exponent-weight product times the actual multilogarithmic contact.
-/

namespace GeneralizedLogarithms.MultivariateLogarithmicContactIdeal

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent

variable {k m : ℕ}

section Algebra

variable {A : Type*} [CommRing A] [Algebra ℂ A]

def centeredY (c : ℂ) (y : A) : A := algebraMap ℂ A c⁻¹ * y - 1

def truncatedCoordinates (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (y : Fin k → A) (x : Fin m → A)
    (T : Fin m → Fin k → ℕ) : (Fin k ⊕ Fin m) → A :=
  Sum.elim (fun r => centeredY (cY r) (y r))
    (fun i => x i - algebraMap ℂ A (cX i) -
      ∑ r, algebraMap ℂ A (a i r : ℂ) *
        Polynomial.aeval (centeredY (cY r) (y r))
          (PowerSeries.trunc (T i r) (PowerSeries.log ℂ)))

def logarithmicIdeal (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (y : Fin k → A) (x : Fin m → A)
    (T : Fin m → Fin k → ℕ) (e : (Fin k ⊕ Fin m) → ℕ) : Ideal A :=
  Ideal.span (Set.range (fun j => truncatedCoordinates a cY cX y x T j ^ e j))

end Algebra

section DVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem logarithmicIdeal_eq_powerIdeal (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (y : Fin k → A) (x : Fin m → A)
    (T : Fin m → Fin k → ℕ) (e : (Fin k ⊕ Fin m) → ℕ) :
    logarithmicIdeal a cY cX y x T e =
      BranchContactIdeal.powerIdeal (truncatedCoordinates a cY cX y x T) e := rfl

theorem expansion_centeredY (c : ℂ) (y : A) :
    DVRBranch.expansion ℂ A (centeredY c y) =
      MultilogBranchCoordinates.centeredY c (DVRBranch.expansion ℂ A y) := by
  simp [centeredY, MultilogBranchCoordinates.centeredY, AlgHom.commutes]

theorem expansion_truncatedCoordinates (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → A) (x : Fin m → A) (T : Fin m → Fin k → ℕ)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (y r) = cY r) :
    (fun j => DVRBranch.expansion ℂ A (truncatedCoordinates a cY cX y x T j)) =
      MultivariateLogTruncation.truncatedBranchCoordinates a cY cX
        (fun r => DVRBranch.expansion ℂ A (y r))
        (fun i => DVRBranch.expansion ℂ A (x i)) T := by
  have hs (r : Fin k) : PowerSeries.HasSubst
      (MultilogBranchCoordinates.centeredY (cY r) (DVRBranch.expansion ℂ A (y r))) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (MultilogBranchCoordinates.constantCoeff_centeredY (cY r) (hcY r) _
        (by simpa using hy r))
  funext j
  cases j with
  | inl r =>
      simp [truncatedCoordinates, MultivariateLogTruncation.truncatedBranchCoordinates,
        expansion_centeredY]
  | inr i =>
      simp only [truncatedCoordinates, MultivariateLogTruncation.truncatedBranchCoordinates,
        Sum.elim_inr, map_sub, map_sum, map_mul, AlgHom.commutes,
        LogarithmicContactIdeal.expansion_polynomial_aeval, expansion_centeredY,
        PowerSeries.subst_coe (hs _)]
      rfl

theorem truncatedCoordinates_nonzero
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j)
    (a : Fin m → Fin k → ℤ) (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (hcY : ∀ r, cY r ≠ 0) (y : Fin k → A) (x : Fin m → A)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (y r) = cY r)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = cX i)
    (hnc : (∃ r, y r ≠ algebraMap ℂ A (cY r)) ∨
      ∃ i, x i ≠ algebraMap ℂ A (cX i))
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r)) :
    ∃ j, truncatedCoordinates a cY cX y x T j ≠ 0 := by
  have hn := MultivariateLogTruncation.truncatedBranchCoordinates_not_all_zero
    v hv a cY cX hcY (fun r => DVRBranch.expansion ℂ A (y r))
    (fun i => DVRBranch.expansion ℂ A (x i))
    (fun r => by simpa using hy r) (fun i => by simpa using hx i)
    (MultilogBranchCoordinates.coordinates_nonzero a cY cX hcY y x hnc) T hT
  rw [← expansion_truncatedCoordinates a cY cX hcY y x T hy] at hn
  obtain ⟨j, hj⟩ := hn
  refine ⟨j, ?_⟩
  intro hz
  apply hj
  change DVRBranch.expansion ℂ A (truncatedCoordinates a cY cX y x T j) = 0
  rw [hz, map_zero]

theorem truncated_contact_eq
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j)
    (a : Fin m → Fin k → ℤ) (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (hcY : ∀ r, cY r ≠ 0) (y : Fin k → A) (x : Fin m → A)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (y r) = cY r)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = cX i)
    (hnc : (∃ r, y r ≠ algebraMap ℂ A (cY r)) ∨
      ∃ i, x i ≠ algebraMap ℂ A (cX i))
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r)) :
    BranchContactIdeal.contact v (truncatedCoordinates a cY cX y x T)
      (truncatedCoordinates_nonzero v hv a cY cX hcY y x hy hx hnc T hT) =
        MultilogBranchCoordinates.contact v a cY cX hcY y x hnc := by
  unfold BranchContactIdeal.contact MultilogBranchCoordinates.contact
  trans BranchContact.contact v
    (MultivariateLogTruncation.truncatedBranchCoordinates a cY cX
      (fun r => DVRBranch.expansion ℂ A (y r))
      (fun i => DVRBranch.expansion ℂ A (x i)) T)
    (MultivariateLogTruncation.truncatedBranchCoordinates_not_all_zero
      v hv a cY cX hcY (fun r => DVRBranch.expansion ℂ A (y r))
      (fun i => DVRBranch.expansion ℂ A (x i))
      (fun r => by simpa using hy r) (fun i => by simpa using hx i)
      (MultilogBranchCoordinates.coordinates_nonzero a cY cX hcY y x hnc) T hT)
  · apply LogarithmicContactIdeal.branchContact_congr
    exact expansion_truncatedCoordinates a cY cX hcY y x T hy
  · exact MultivariateLogTruncation.contact_truncatedBranchCoordinates_eq
      v hv a cY cX hcY (fun r => DVRBranch.expansion ℂ A (y r))
      (fun i => DVRBranch.expansion ℂ A (x i))
      (fun r => by simpa using hy r) (fun i => by simpa using hx i)
      (MultilogBranchCoordinates.coordinates_nonzero a cY cX hcY y x hnc) T hT

theorem logarithmicIdeal_colength_eq_contact
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j)
    (a : Fin m → Fin k → ℤ) (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (hcY : ∀ r, cY r ≠ 0) (y : Fin k → A) (x : Fin m → A)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (y r) = cY r)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = cX i)
    (hnc : (∃ r, y r ≠ algebraMap ℂ A (cY r)) ∨
      ∃ i, x i ≠ algebraMap ℂ A (cX i))
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (e : (Fin k ⊕ Fin m) → ℕ) (he : ∀ j, v j * (e j : ℚ) = R) :
    ((Module.length A (A ⧸ logarithmicIdeal a cY cX y x T e)).toNat : ℚ) =
      R * MultilogBranchCoordinates.contact v a cY cX hcY y x hnc := by
  rw [logarithmicIdeal_eq_powerIdeal,
    BranchContactIdeal.colength_eq_contact v hv _
      (truncatedCoordinates_nonzero v hv a cY cX hcY y x hy hx hnc T hT) R e he,
    truncated_contact_eq v hv a cY cX hcY y x hy hx hnc T hT]

theorem logarithmicIdeal_colength_ne_top
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j)
    (a : Fin m → Fin k → ℤ) (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (hcY : ∀ r, cY r ≠ 0) (y : Fin k → A) (x : Fin m → A)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (y r) = cY r)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = cX i)
    (hnc : (∃ r, y r ≠ algebraMap ℂ A (cY r)) ∨
      ∃ i, x i ≠ algebraMap ℂ A (cX i))
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (e : (Fin k ⊕ Fin m) → ℕ) (he : ∀ j, v j * (e j : ℚ) = R) :
    Module.length A (A ⧸ logarithmicIdeal a cY cX y x T e) ≠ ⊤ := by
  obtain ⟨j, hj, heq, _⟩ := BranchContactIdeal.exists_generator_colength_eq_contact
    v hv (truncatedCoordinates a cY cX y x T)
    (truncatedCoordinates_nonzero v hv a cY cX hcY y x hy hx hnc T hT) R e he
  rw [logarithmicIdeal_eq_powerIdeal, heq]
  exact CurveLocalOrder.principal_colength_ne_top (pow_ne_zero _ hj)

end DVR

section Places

open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch

variable {E : Type*} [Field E] [Algebra ℂ E]

/-- The local ideal identity at an actual normalized place, with contact defined
using the same lifted coordinates as the checked multivariate curve inequality. -/
theorem logarithmicIdeal_colength_eq_placeContact
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j)
    (a : Fin m → Fin k → ℤ) (z : (Fin k ⊕ Fin m) → E)
    (c : (Fin k ⊕ Fin m) → ℂ) (hcY : ∀ r, c (Sum.inl r) ≠ 0)
    (hc : Centered z c p) (hnc : ∃ j, z j ≠ algebraMap ℂ E (c j))
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (e : (Fin k ⊕ Fin m) → ℕ) (he : ∀ j, v j * (e j : ℚ) = R) :
    ((Module.length (ring p) ((ring p) ⧸
      logarithmicIdeal a (fun r => c (Sum.inl r)) (fun i => c (Sum.inr i))
        (fun r => lift p z c hc (Sum.inl r))
        (fun i => lift p z c hc (Sum.inr i)) T e)).toNat : ℚ) =
      R * MultilogBranchCoordinates.placeContact p a z c hcY hc hnc v := by
  exact logarithmicIdeal_colength_eq_contact v hv a _ _ hcY _ _
    (fun r => lift_residue p z c hc (Sum.inl r))
    (fun i => lift_residue p z c hc (Sum.inr i))
    (MultilogBranchCoordinates.lifted_nonconstant p z c hc hnc) T hT R e he

end Places

end
end GeneralizedLogarithms.MultivariateLogarithmicContactIdeal

/-- info: 'GeneralizedLogarithms.MultivariateLogarithmicContactIdeal.truncated_contact_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogarithmicContactIdeal.truncated_contact_eq

/-- info: 'GeneralizedLogarithms.MultivariateLogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact

/-- info: 'GeneralizedLogarithms.MultivariateLogarithmicContactIdeal.logarithmicIdeal_colength_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogarithmicContactIdeal.logarithmicIdeal_colength_ne_top

/-- info: 'GeneralizedLogarithms.MultivariateLogarithmicContactIdeal.logarithmicIdeal_colength_eq_placeContact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogarithmicContactIdeal.logarithmicIdeal_colength_eq_placeContact
