import GeneralizedLogarithms.MultivariateLogPolynomialAdapter
import LogIrrationalityMeasure.Jets.JetProductLocalization

/-!
# Localizing the product of multilogarithmic center ideals

Injectivity of the whole longitudinal center tuple makes every nonselected
center ideal a unit ideal at a selected center. Thus the product localizes to
the selected ideal and has the colength calculated by actual multilog contact.
-/

namespace GeneralizedLogarithms.MultivariateJetProductLocalization

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateLogPolynomialAdapter MultivariateLogarithmicContactIdeal

variable {k m : ℕ}

def polynomialIdeal {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → (Fin k ⊕ Fin m) → ℂ)
    (T : Fin m → Fin k → ℕ) (e : (Fin k ⊕ Fin m) → ℕ) :
    Ideal (MvPolynomial (Fin k ⊕ Fin m) ℂ) :=
  ∏ j, logPowerIdeal a (c j) T e

section Algebra

variable {A : Type*} [CommRing A] [Algebra ℂ A]

theorem map_polynomialIdeal {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → (Fin k ⊕ Fin m) → ℂ)
    (T : Fin m → Fin k → ℕ) (e : (Fin k ⊕ Fin m) → ℕ)
    (z : (Fin k ⊕ Fin m) → A) :
    (polynomialIdeal a c T e).map (MvPolynomial.aeval z).toRingHom =
      ∏ j, logarithmicIdeal a (fun r => c j (Sum.inl r)) (fun i => c j (Sum.inr i))
        (fun r => z (Sum.inl r)) (fun i => z (Sum.inr i)) T e := by
  unfold polynomialIdeal
  change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact map_logPowerIdeal_aeval a (c j) T e z

end Algebra

section Local

variable {A : Type*} [CommRing A] [IsLocalRing A] [Algebra ℂ A]
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem logarithmicIdeal_eq_top_of_longitudinal_residue_ne
    (a : Fin m → Fin k → ℤ) (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (hcY : ∀ r, cY r ≠ 0) (y : Fin k → A) (x : Fin m → A)
    (T : Fin m → Fin k → ℕ) (e : (Fin k ⊕ Fin m) → ℕ)
    (hne : ∃ r, CurveLocalOrder.residueAugmentation ℂ A (y r) ≠ cY r) :
    logarithmicIdeal a cY cX y x T e = ⊤ := by
  obtain ⟨r, hr⟩ := hne
  have hunit : IsUnit (centeredY (cY r) (y r)) := by
    apply (JetProductLocalization.residue_ne_zero_iff_isUnit _).mp
    simp only [centeredY, map_sub, map_mul, map_one,
      CurveLocalOrder.residueAugmentation_algebraMap]
    intro hz
    apply hr
    have h1 : (cY r)⁻¹ * CurveLocalOrder.residueAugmentation ℂ A (y r) = 1 :=
      sub_eq_zero.mp hz
    calc
      CurveLocalOrder.residueAugmentation ℂ A (y r) =
          cY r * ((cY r)⁻¹ * CurveLocalOrder.residueAugmentation ℂ A (y r)) := by
        rw [← mul_assoc, mul_inv_cancel₀ (hcY r), one_mul]
      _ = cY r := by rw [h1, mul_one]
  apply Ideal.eq_top_of_isUnit_mem _
    (show truncatedCoordinates a cY cX y x T (Sum.inl r) ^ e (Sum.inl r) ∈
      logarithmicIdeal a cY cX y x T e from
        Ideal.subset_span (Set.mem_range_self (Sum.inl r)))
  exact hunit.pow (e (Sum.inl r))

theorem map_logPowerIdeal_eq_top_of_ne {J : Type*}
    (a : Fin m → Fin k → ℤ) (c : J → (Fin k ⊕ Fin m) → ℂ)
    (hc : Function.Injective (fun j r => c j (Sum.inl r)))
    (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : (Fin k ⊕ Fin m) → ℕ)
    (z : (Fin k ⊕ Fin m) → A) (j q : J) (hqj : q ≠ j)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (z (Sum.inl r)) = c j (Sum.inl r)) :
    (logPowerIdeal a (c q) T e).map (MvPolynomial.aeval z).toRingHom = ⊤ := by
  rw [map_logPowerIdeal_aeval]
  apply logarithmicIdeal_eq_top_of_longitudinal_residue_ne a _ _ (hcY q)
  by_contra h
  push Not at h
  apply hqj
  apply hc
  funext r
  exact (h r).symm.trans (hy r)

/-- Only longitudinal residue matching is needed to select the factor. -/
theorem map_polynomialIdeal_eq_selected {J : Type*} [Fintype J]
    (a : Fin m → Fin k → ℤ) (c : J → (Fin k ⊕ Fin m) → ℂ)
    (hc : Function.Injective (fun j r => c j (Sum.inl r)))
    (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (T : Fin m → Fin k → ℕ) (e : (Fin k ⊕ Fin m) → ℕ)
    (z : (Fin k ⊕ Fin m) → A) (j : J)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (z (Sum.inl r)) = c j (Sum.inl r)) :
    (polynomialIdeal a c T e).map (MvPolynomial.aeval z).toRingHom =
      logarithmicIdeal a (fun r => c j (Sum.inl r)) (fun i => c j (Sum.inr i))
        (fun r => z (Sum.inl r)) (fun i => z (Sum.inr i)) T e := by
  classical
  rw [map_polynomialIdeal]
  apply Finset.prod_eq_single j
  · intro q _ hqj
    rw [Ideal.one_eq_top, ← map_logPowerIdeal_aeval a (c q) T e z]
    exact map_logPowerIdeal_eq_top_of_ne a c hc hcY T e z j q hqj hy
  · simp

end Local

section DVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem polynomialIdeal_colength_eq_contact {J : Type*} [Fintype J]
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ s, 0 < v s)
    (a : Fin m → Fin k → ℤ) (c : J → (Fin k ⊕ Fin m) → ℂ)
    (hc : Function.Injective (fun j r => c j (Sum.inl r)))
    (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (z : (Fin k ⊕ Fin m) → A) (j : J)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (z (Sum.inl r)) = c j (Sum.inl r))
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (z (Sum.inr i)) = c j (Sum.inr i))
    (hnc : (∃ r, z (Sum.inl r) ≠ algebraMap ℂ A (c j (Sum.inl r))) ∨
      ∃ i, z (Sum.inr i) ≠ algebraMap ℂ A (c j (Sum.inr i)))
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (e : (Fin k ⊕ Fin m) → ℕ) (he : ∀ s, v s * (e s : ℚ) = R) :
    ((Module.length A (A ⧸
      (polynomialIdeal a c T e).map (MvPolynomial.aeval z).toRingHom)).toNat : ℚ) =
      R * MultilogBranchCoordinates.contact v a
        (fun r => c j (Sum.inl r)) (fun i => c j (Sum.inr i)) (hcY j)
        (fun r => z (Sum.inl r)) (fun i => z (Sum.inr i)) hnc := by
  rw [map_polynomialIdeal_eq_selected a c hc hcY T e z j hy]
  exact logarithmicIdeal_colength_eq_contact v hv a _ _ (hcY j) _ _ hy hx hnc T hT R e he

end DVR

section Places

open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch

variable {E : Type*} [Field E] [Algebra ℂ E]

theorem polynomialIdeal_colength_eq_placeContact {J : Type*} [Fintype J]
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ s, 0 < v s)
    (a : Fin m → Fin k → ℤ) (c : J → (Fin k ⊕ Fin m) → ℂ)
    (hc : Function.Injective (fun j r => c j (Sum.inl r)))
    (hcY : ∀ j r, c j (Sum.inl r) ≠ 0)
    (z : (Fin k ⊕ Fin m) → E) (j : J) (hcenter : Centered z (c j) p)
    (hnc : ∃ s, z s ≠ algebraMap ℂ E (c j s))
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (e : (Fin k ⊕ Fin m) → ℕ) (he : ∀ s, v s * (e s : ℚ) = R) :
    ((Module.length (ring p) ((ring p) ⧸ (polynomialIdeal a c T e).map
      (MvPolynomial.aeval (lift p z (c j) hcenter)).toRingHom)).toNat : ℚ) =
      R * MultilogBranchCoordinates.placeContact p a z (c j) (hcY j) hcenter hnc v := by
  rw [map_polynomialIdeal_eq_selected a c hc hcY T e _ j
    (fun r => lift_residue p z (c j) hcenter (Sum.inl r))]
  exact logarithmicIdeal_colength_eq_placeContact p v hv a z (c j) (hcY j)
    hcenter hnc T hT R e he

end Places

end
end GeneralizedLogarithms.MultivariateJetProductLocalization

/-- info: 'GeneralizedLogarithms.MultivariateJetProductLocalization.map_polynomialIdeal_eq_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateJetProductLocalization.map_polynomialIdeal_eq_selected

/-- info: 'GeneralizedLogarithms.MultivariateJetProductLocalization.polynomialIdeal_colength_eq_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateJetProductLocalization.polynomialIdeal_colength_eq_contact

/-- info: 'GeneralizedLogarithms.MultivariateJetProductLocalization.polynomialIdeal_colength_eq_placeContact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateJetProductLocalization.polynomialIdeal_colength_eq_placeContact
