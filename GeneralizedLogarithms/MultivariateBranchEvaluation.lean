import GeneralizedLogarithms.MultivariateFormalJet
import GeneralizedLogarithms.MultilogBranchCoordinates

/-!
# Multilogarithmic jets along branches and at places

Substitution of the actual multilog branch coordinates in the formal jet
recovers polynomial evaluation. Weighted jet vanishing then gives an order
bound for every frame word, first for series, then in a DVR, and finally at
a normalized place. No derivative-order estimate is assumed here.
-/

namespace GeneralizedLogarithms.MultivariateBranchEvaluation

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open MultivariateFormalJet MultivariateMultiplicity MultilogBranchCoordinates

variable {k m : ℕ}

theorem formalJet_subst_branch (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : ∀ r, PowerSeries.constantCoeff (y r) = c (Sum.inl r))
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c (Sum.inr i))
    (f : MvPolynomial (Fin k ⊕ Fin m) ℂ) :
    MvPowerSeries.subst
      (branchCoordinates a (fun r => c (Sum.inl r)) (fun i => c (Sum.inr i)) y x)
      (formalJet a c f) = MvPolynomial.aeval (Sum.elim y x) f := by
  let ha := branchCoordinates_hasSubst a (fun r => c (Sum.inl r))
    (fun i => c (Sum.inr i)) hc y x hy hx
  have heq : (MvPowerSeries.substAlgHom ha).comp (formalJet a c) =
      MvPolynomial.aeval (Sum.elim y x) := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | inl r =>
      simp only [AlgHom.comp_apply, formalJet_Y, map_mul, map_add, map_one,
        MvPowerSeries.substAlgHom_X, MvPolynomial.aeval_X, Sum.elim_inl]
      rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C]
      change PowerSeries.C (c (Sum.inl r)) *
        (1 + centeredY (c (Sum.inl r)) (y r)) = y r
      simp only [centeredY, add_sub_cancel, ← mul_assoc, ← map_mul,
        mul_inv_cancel₀ (hc r), map_one, one_mul]
    | inr i =>
      simp only [AlgHom.comp_apply, formalJet_X, map_add, map_sum, map_mul,
        MvPowerSeries.substAlgHom_X, MvPolynomial.aeval_X, Sum.elim_inr]
      have hl (r : Fin k) : MvPowerSeries.substAlgHom ha (formalLog r) =
          PowerSeries.subst (centeredY (c (Sum.inl r)) (y r)) (PowerSeries.log ℂ) := by
        rw [MvPowerSeries.substAlgHom_apply, formalLog,
          PowerSeries.subst_toMvPowerSeries ha]
        rfl
      simp only [hl, MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C]
      change PowerSeries.C (c (Sum.inr i)) +
        (x i - PowerSeries.C (c (Sum.inr i)) -
          ∑ r, PowerSeries.C (a i r : ℂ) *
            PowerSeries.subst (centeredY (c (Sum.inl r)) (y r)) (PowerSeries.log ℂ)) +
        (∑ r, PowerSeries.C (a i r : ℂ) *
          PowerSeries.subst (centeredY (c (Sum.inl r)) (y r)) (PowerSeries.log ℂ)) = x i
      ring
  simpa only [AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply] using
    AlgHom.congr_fun heq f

theorem frameWord_branch_order (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : ∀ r, PowerSeries.constantCoeff (y r) = c (Sum.inl r))
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c (Sum.inr i))
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 ≤ v j) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPolynomial (Fin k ⊕ Fin m) ℂ)
    (hf : formalJet a c f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ j (n : ℕ),
      (branchCoordinates a (fun r => c (Sum.inl r)) (fun i => c (Sum.inr i)) y x j).order =
        (n : ℕ∞) → μ * v j ≤ (n : ℚ)) (word : List (Fin k ⊕ Fin m)) :
    (⌈μ * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤ PowerSeries.order
      (MvPolynomial.aeval (Sum.elim y x) (frameWord (fun i r => (a i r : ℂ)) word f)) := by
  have h := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv μ (H - (word.map v).sum) hμ
    (formalJet a c (frameWord (fun i r => (a i r : ℂ)) word f))
    (branchCoordinates a (fun r => c (Sum.inl r)) (fun i => c (Sum.inr i)) y x)
    (branchCoordinates_hasSubst a _ _ hc y x hy hx)
    (formalJet_polynomialFrameWord_vanishing a c v hv H f hf word) hcontact
  rwa [formalJet_subst_branch a c hc y x hy hx] at h

theorem frameWord_branch_order_toNat (a : Fin m → Fin k → ℤ)
    (c : (Fin k ⊕ Fin m) → ℂ) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : ∀ r, PowerSeries.constantCoeff (y r) = c (Sum.inl r))
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c (Sum.inr i))
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 ≤ v j) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPolynomial (Fin k ⊕ Fin m) ℂ)
    (hf : formalJet a c f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ j (n : ℕ),
      (branchCoordinates a (fun r => c (Sum.inl r)) (fun i => c (Sum.inr i)) y x j).order =
        (n : ℕ∞) → μ * v j ≤ (n : ℚ)) (word : List (Fin k ⊕ Fin m))
    (hne : MvPolynomial.aeval (Sum.elim y x) (frameWord (fun i r => (a i r : ℂ)) word f) ≠ 0) :
    μ * (H - (word.map v).sum) ≤
      ((PowerSeries.order (MvPolynomial.aeval (Sum.elim y x)
        (frameWord (fun i r => (a i r : ℂ)) word f))).toNat : ℚ) := by
  have h := frameWord_branch_order a c hc y x hy hx v hv μ H hμ f hf hcontact word
  have hn := PowerSeries.order_eq_top.not.mpr hne
  exact Nat.ceil_le.mp (by simpa using ENat.toNat_le_toNat h hn)

section DVR

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem expansion_aeval {ι : Type*} (z : ι → A) (f : MvPolynomial ι ℂ) :
    DVRBranch.expansion ℂ A (MvPolynomial.aeval z f) =
      MvPolynomial.aeval (fun j => DVRBranch.expansion ℂ A (z j)) f := by
  have he : (DVRBranch.expansion ℂ A).comp (MvPolynomial.aeval z) =
      MvPolynomial.aeval (fun j => DVRBranch.expansion ℂ A (z j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp
  exact AlgHom.congr_fun he f

theorem frameWord_addVal_lower (a : Fin m → Fin k → ℤ)
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ)
    (c : (Fin k ⊕ Fin m) → ℂ) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (y : Fin k → A) (x : Fin m → A)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (y r) = c (Sum.inl r))
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c (Sum.inr i))
    (hnc : (∃ r, y r ≠ algebraMap ℂ A (c (Sum.inl r))) ∨
      ∃ i, x i ≠ algebraMap ℂ A (c (Sum.inr i)))
    (f : MvPolynomial (Fin k ⊕ Fin m) ℂ)
    (hf : formalJet a c f ∈ JetGeometry.rationalWeightedIdeal v (fun j => (hv j).le) H)
    (word : List (Fin k ⊕ Fin m))
    (hne : MvPolynomial.aeval (Sum.elim y x) (frameWord (fun i r => (a i r : ℂ)) word f) ≠ 0) :
    MultilogBranchCoordinates.contact v a (fun r => c (Sum.inl r))
      (fun i => c (Sum.inr i)) hc y x hnc * (H - (word.map v).sum) ≤
      ((IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval (Sum.elim y x) (frameWord (fun i r => (a i r : ℂ)) word f))).toNat : ℚ) := by
  have heval (g : MvPolynomial (Fin k ⊕ Fin m) ℂ) :
      DVRBranch.expansion ℂ A (MvPolynomial.aeval (Sum.elim y x) g) =
      MvPolynomial.aeval (Sum.elim (fun r => DVRBranch.expansion ℂ A (y r))
        (fun i => DVRBranch.expansion ℂ A (x i))) g := by
    rw [expansion_aeval]
    apply congrArg (fun z => MvPolynomial.aeval z g)
    funext j
    cases j <;> rfl
  have hne' : MvPolynomial.aeval (Sum.elim (fun r => DVRBranch.expansion ℂ A (y r))
      (fun i => DVRBranch.expansion ℂ A (x i))) (frameWord (fun i r => (a i r : ℂ)) word f) ≠ 0 := by
    rw [← heval]
    exact (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hne
  have hb := frameWord_branch_order_toNat a c hc
    (fun r => DVRBranch.expansion ℂ A (y r)) (fun i => DVRBranch.expansion ℂ A (x i))
    (fun r => by simpa using hy r) (fun i => by simpa using hx i)
    v (fun j => (hv j).le)
    (MultilogBranchCoordinates.contact v a _ _ hc y x hnc) H
    (MultilogBranchCoordinates.contact_pos v hv a _ _ hc y x hy hx hnc).le f hf
    (BranchContact.contact_bound v hv _ _) word hne'
  rw [← heval, DVRBranch.expansion_order] at hb
  exact hb

theorem frameWord_colength_lower (a : Fin m → Fin k → ℤ)
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ)
    (c : (Fin k ⊕ Fin m) → ℂ) (hc : ∀ r, c (Sum.inl r) ≠ 0)
    (y : Fin k → A) (x : Fin m → A)
    (hy : ∀ r, CurveLocalOrder.residueAugmentation ℂ A (y r) = c (Sum.inl r))
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c (Sum.inr i))
    (hnc : (∃ r, y r ≠ algebraMap ℂ A (c (Sum.inl r))) ∨
      ∃ i, x i ≠ algebraMap ℂ A (c (Sum.inr i)))
    (f : MvPolynomial (Fin k ⊕ Fin m) ℂ)
    (hf : formalJet a c f ∈ JetGeometry.rationalWeightedIdeal v (fun j => (hv j).le) H)
    (word : List (Fin k ⊕ Fin m))
    (hne : MvPolynomial.aeval (Sum.elim y x) (frameWord (fun i r => (a i r : ℂ)) word f) ≠ 0) :
    MultilogBranchCoordinates.contact v a (fun r => c (Sum.inl r))
      (fun i => c (Sum.inr i)) hc y x hnc * (H - (word.map v).sum) ≤
      ((Module.length A (A ⧸ Ideal.span {
        MvPolynomial.aeval (Sum.elim y x) (frameWord (fun i r => (a i r : ℂ)) word f)})).toNat : ℚ) := by
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hne]
  exact frameWord_addVal_lower a v hv H c hc y x hy hx hnc f hf word hne

end DVR

section Places

open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch

variable {E : Type*} [Field E] [Algebra ℂ E]
  (p : NormalizedPlace ℂ E)
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem frameWord_field_order_lower (a : Fin m → Fin k → ℤ)
    (z : (Fin k ⊕ Fin m) → E) (c : (Fin k ⊕ Fin m) → ℂ)
    (hcY : ∀ r, c (Sum.inl r) ≠ 0) (hc : Centered z c p)
    (hnc : ∃ j, z j ≠ algebraMap ℂ E (c j))
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j) (H : ℚ)
    (f : MvPolynomial (Fin k ⊕ Fin m) ℂ)
    (hf : formalJet a c f ∈ JetGeometry.rationalWeightedIdeal v (fun j => (hv j).le) H)
    (word : List (Fin k ⊕ Fin m))
    (hne : MvPolynomial.aeval z (frameWord (fun i r => (a i r : ℂ)) word f) ≠ 0) :
    placeContact p a z c hcY hc hnc v * (H - (word.map v).sum) ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation
        (MvPolynomial.aeval z (frameWord (fun i r => (a i r : ℂ)) word f)) : ℚ) := by
  let x := lift p z c hc
  have he : Sum.elim (fun r => x (Sum.inl r)) (fun i => x (Sum.inr i)) = x := by
    funext j
    cases j <;> rfl
  have hn : MvPolynomial.aeval x (frameWord (fun i r => (a i r : ℂ)) word f) ≠ 0 := by
    intro hz
    apply hne
    rw [← lift_aeval p z c hc, hz, map_zero]
  have hb := frameWord_colength_lower a v hv H c hcY
    (fun r => x (Sum.inl r)) (fun i => x (Sum.inr i))
    (fun r => lift_residue p z c hc (Sum.inl r))
    (fun i => lift_residue p z c hc (Sum.inr i))
    (lifted_nonconstant p z c hc hnc) f hf word (he.symm ▸ hn)
  have heval := congrArg (fun u =>
    MvPolynomial.aeval u (frameWord (fun i r => (a i r : ℂ)) word f)) he
  rw [heval] at hb
  rw [coordinateOrder_aeval_eq_length p z c hc _ hne]
  simpa only [Int.cast_natCast, placeContact, x] using hb

end Places
end
end GeneralizedLogarithms.MultivariateBranchEvaluation

/-- info: 'GeneralizedLogarithms.MultivariateBranchEvaluation.formalJet_subst_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateBranchEvaluation.formalJet_subst_branch

/-- info: 'GeneralizedLogarithms.MultivariateBranchEvaluation.frameWord_branch_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateBranchEvaluation.frameWord_branch_order

/-- info: 'GeneralizedLogarithms.MultivariateBranchEvaluation.frameWord_field_order_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateBranchEvaluation.frameWord_field_order_lower
