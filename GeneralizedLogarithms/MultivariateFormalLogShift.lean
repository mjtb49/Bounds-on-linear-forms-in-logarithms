import GeneralizedLogarithms.MultivariateFormalJet
import GeneralizedLogarithms.MultivariateLogPolynomialAdapter
import LogIrrationalityMeasure.Analysis.FormalLogTruncation

/-!
# Formal shifts from truncated to actual multilogarithmic jets

All longitudinal variables are fixed. Each transverse variable is translated
by a finite sum of series in the individual longitudinal variables. Applying
this automorphism to the truncated jet produces the actual formal jet.
The logarithmic tails preserve the weighted filtration at the stated cutoffs.
-/

namespace GeneralizedLogarithms.MultivariateFormalLogShift

noncomputable section
open scoped BigOperators
open MvPowerSeries
open LogIrrationalityMeasure.LogExponent
open JetGeometry

variable {R : Type*} [CommRing R] {k m : ℕ}

def shiftVars (tail : Fin m → Fin k → PowerSeries R) :
    Fin k ⊕ Fin m → MvPowerSeries (Fin k ⊕ Fin m) R :=
  Sum.elim (fun r => X (Sum.inl r))
    (fun i => X (Sum.inr i) + ∑ r, (tail i r).toMvPowerSeries (Sum.inl r))

theorem shiftVars_hasSubst (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) : HasSubst (shiftVars tail) := by
  apply hasSubst_of_constantCoeff_zero
  intro j
  cases j with
  | inl r => simp [shiftVars]
  | inr i =>
    simp only [shiftVars, Sum.elim_inr, map_add, constantCoeff_X, map_sum,
      PowerSeries.toMvPowerSeries_apply, constantCoeff_rename, zero_add]
    exact Finset.sum_eq_zero (fun r _ => ht i r)

def shiftMap (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) :
    MvPowerSeries (Fin k ⊕ Fin m) R →ₐ[R] MvPowerSeries (Fin k ⊕ Fin m) R :=
  substAlgHom (shiftVars_hasSubst tail ht)

@[simp] theorem shiftMap_X_inl (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) (r : Fin k) :
    shiftMap tail ht (X (Sum.inl r)) = X (Sum.inl r) := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_X_inr (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) (i : Fin m) :
    shiftMap tail ht (X (Sum.inr i)) =
      X (Sum.inr i) + ∑ r, (tail i r).toMvPowerSeries (Sum.inl r) := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_toMvPowerSeries (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) (r : Fin k) (f : PowerSeries R) :
    shiftMap tail ht (f.toMvPowerSeries (Sum.inl r)) = f.toMvPowerSeries (Sum.inl r) := by
  rw [shiftMap, substAlgHom_apply,
    PowerSeries.subst_toMvPowerSeries (shiftVars_hasSubst tail ht)]
  change PowerSeries.subst (X (Sum.inl r : Fin k ⊕ Fin m)) f = _
  exact PowerSeries.toMvPowerSeries_eq_subst.symm

@[simp] theorem shiftMap_C (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) (z : R) :
    shiftMap tail ht (C z) = C z := (shiftMap tail ht).commutes z

theorem shiftMap_apply (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) (f) :
    shiftMap tail ht f = subst (shiftVars tail) f := substAlgHom_apply _ _

theorem shiftMap_inverse (s t : Fin m → Fin k → PowerSeries R)
    (hs : ∀ i r, PowerSeries.constantCoeff (s i r) = 0)
    (ht : ∀ i r, PowerSeries.constantCoeff (t i r) = 0)
    (hst : ∀ i r, s i r + t i r = 0) (f : MvPowerSeries (Fin k ⊕ Fin m) R) :
    shiftMap s hs (shiftMap t ht f) = f := by
  simp only [shiftMap_apply]
  rw [subst_comp_subst_apply (shiftVars_hasSubst t ht) (shiftVars_hasSubst s hs)]
  have hvars : (fun j => subst (shiftVars s) (shiftVars t j)) = X := by
    funext j
    rw [← shiftMap_apply s hs]
    cases j with
    | inl r => exact shiftMap_X_inl s hs r
    | inr i =>
      change shiftMap s hs (X (Sum.inr i) + ∑ r, (t i r).toMvPowerSeries (Sum.inl r)) = _
      simp only [map_add, shiftMap_X_inr, map_sum, shiftMap_toMvPowerSeries]
      rw [add_assoc, ← Finset.sum_add_distrib]
      simp only [← map_add, hst, map_zero, Finset.sum_const_zero, add_zero]
  rw [hvars]
  exact congrFun subst_self f

def shiftEquiv (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) :
    MvPowerSeries (Fin k ⊕ Fin m) R ≃ₐ[R] MvPowerSeries (Fin k ⊕ Fin m) R := by
  let hn : ∀ i r, PowerSeries.constantCoeff (-tail i r) = 0 := by simp [ht]
  refine AlgEquiv.ofAlgHom (shiftMap tail ht) (shiftMap (fun i r => -tail i r) hn) ?_ ?_
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse tail (fun i r => -tail i r) ht hn (fun i r => add_neg_cancel _) f
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse (fun i r => -tail i r) tail hn ht (fun i r => neg_add_cancel _) f

@[simp] theorem shiftEquiv_apply (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) (f) :
    shiftEquiv tail ht f = shiftMap tail ht f := rfl

@[simp] theorem shiftEquiv_symm_apply (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0) (f) :
    (shiftEquiv tail ht).symm f = shiftMap (fun i r => -tail i r) (by simp [ht]) f := rfl

theorem shiftMap_mem_rationalWeightedIdeal (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 ≤ v j)
    (hweight : ∀ i r, (tail i r).toMvPowerSeries (Sum.inl r) ∈
      rationalWeightedIdeal v hv (v (Sum.inr i))) (H : ℚ)
    (f : MvPowerSeries (Fin k ⊕ Fin m) R) (hf : f ∈ rationalWeightedIdeal v hv H) :
    shiftMap tail ht f ∈ rationalWeightedIdeal v hv H := by
  rw [shiftMap_apply]
  apply FormalLogTruncation.subst_mem_rationalWeightedIdeal v v hv hv _
    (shiftVars_hasSubst tail ht) _ H f hf
  intro j
  cases j with
  | inl r => exact FormalLogTruncation.X_mem_rationalWeightedIdeal v hv _
  | inr i =>
    exact Ideal.add_mem _ (FormalLogTruncation.X_mem_rationalWeightedIdeal v hv _)
      (Ideal.sum_mem _ (fun r _ => hweight i r))

theorem shiftEquiv_mem_iff (tail : Fin m → Fin k → PowerSeries R)
    (ht : ∀ i r, PowerSeries.constantCoeff (tail i r) = 0)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 ≤ v j)
    (hweight : ∀ i r, (tail i r).toMvPowerSeries (Sum.inl r) ∈
      rationalWeightedIdeal v hv (v (Sum.inr i))) (H : ℚ) (f) :
    shiftEquiv tail ht f ∈ rationalWeightedIdeal v hv H ↔
      f ∈ rationalWeightedIdeal v hv H := by
  have hn : ∀ i r, (-tail i r).toMvPowerSeries (Sum.inl r) ∈
      rationalWeightedIdeal v hv (v (Sum.inr i)) := by
    intro i r
    rw [map_neg]
    intro d hd
    rw [map_neg, hweight i r d hd, neg_zero]
  constructor
  · intro hf
    have h := shiftMap_mem_rationalWeightedIdeal (fun i r => -tail i r)
      (by simp [ht]) v hv hn H _ hf
    change (shiftEquiv tail ht).symm (shiftEquiv tail ht f) ∈ _ at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · exact shiftMap_mem_rationalWeightedIdeal tail ht v hv hweight H f

theorem logTail_mem_rationalWeightedIdeal {σ : Type*}
    (v : σ → ℚ) (hv : ∀ j, 0 ≤ v j) (j : σ) (T : ℕ) (H : ℚ)
    (hT : H ≤ (T : ℚ) * v j) :
    (FormalLogTruncation.logTail T).toMvPowerSeries j ∈ rationalWeightedIdeal v hv H := by
  classical
  intro d hd
  rw [PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.coeff_subst_single]
  by_cases he : d = Finsupp.single j (d j)
  · rw [ite_eq_left he]
    have hdeg : (d j : ℚ) * v j < H := by
      calc
        (d j : ℚ) * v j = Finsupp.weight v (Finsupp.single j (d j)) := by
          rw [Finsupp.weight_single, nsmul_eq_mul]
        _ = Finsupp.weight v d := congrArg _ he.symm
        _ < H := hd
    apply FormalLogTruncation.coeff_logTail_eq_zero
    by_contra hn
    have hcast : (T : ℚ) ≤ d j := by exact_mod_cast Nat.le_of_not_gt hn
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hcast (hv j)).trans' hT)) hdeg
  · exact ite_eq_right he

def logarithmicTails (a : Fin m → Fin k → ℤ) (T : Fin m → Fin k → ℕ) :
    Fin m → Fin k → PowerSeries ℂ :=
  fun i r => PowerSeries.C (a i r : ℂ) * FormalLogTruncation.logTail (T i r)

@[simp] theorem logarithmicTails_constantCoeff (a : Fin m → Fin k → ℤ)
    (T : Fin m → Fin k → ℕ) (i : Fin m) (r : Fin k) :
    PowerSeries.constantCoeff (logarithmicTails a T i r) = 0 := by
  simp [logarithmicTails]

theorem logarithmicTails_mem (a : Fin m → Fin k → ℤ) (T : Fin m → Fin k → ℕ)
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 ≤ v j)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r)) (i : Fin m) (r : Fin k) :
    (logarithmicTails a T i r).toMvPowerSeries (Sum.inl r) ∈
      rationalWeightedIdeal v hv (v (Sum.inr i)) := by
  rw [logarithmicTails, map_mul]
  exact Ideal.mul_mem_left _ _ (logTail_mem_rationalWeightedIdeal v hv _ _ _ (hT i r))

theorem truncatedFormalJet_Y (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (T : Fin m → Fin k → ℕ) (r : Fin k) :
    MultivariateLogPolynomialAdapter.truncatedFormalJet a c T (MvPolynomial.X (Sum.inl r)) =
      C (c (Sum.inl r)) * (1 + X (Sum.inl r)) := by
  simp [MultivariateLogPolynomialAdapter.truncatedFormalJet,
    MultivariateCompactJetPolynomial.triangularMap]

theorem truncatedFormalJet_X (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (T : Fin m → Fin k → ℕ) (i : Fin m) :
    MultivariateLogPolynomialAdapter.truncatedFormalJet a c T (MvPolynomial.X (Sum.inr i)) =
      C (c (Sum.inr i)) + X (Sum.inr i) + ∑ r, C (a i r : ℂ) *
        (PowerSeries.trunc (T i r) (PowerSeries.log ℂ) : PowerSeries ℂ).toMvPowerSeries
          (Sum.inl r) := by
  simp only [MultivariateLogPolynomialAdapter.truncatedFormalJet, AlgHom.comp_apply,
    MultivariateCompactJetPolynomial.triangularMap_X_inr, map_add,
    MultivariateLogPolynomialAdapter.aeval_logPolynomials, map_sum, map_mul,
    ← Polynomial.aeval_algHom_apply]
  simp only [MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.algebraMap_self,
    MvPowerSeries.map_id, RingHom.id_apply, MvPolynomial.algebraMap_eq,
    MvPolynomial.coe_C, MvPolynomial.coe_X,
    PowerSeries.toMvPowerSeries_eq_subst, PowerSeries.subst_coe (PowerSeries.HasSubst.X _)]

theorem shiftMap_truncatedFormalJet (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (T : Fin m → Fin k → ℕ) (P : MvPolynomial (Fin k ⊕ Fin m) ℂ) :
    shiftMap (logarithmicTails a T) (logarithmicTails_constantCoeff a T)
      (MultivariateLogPolynomialAdapter.truncatedFormalJet a c T P) =
      MultivariateFormalJet.formalJet a c P := by
  have he : (shiftMap (logarithmicTails a T) (logarithmicTails_constantCoeff a T)).comp
      (MultivariateLogPolynomialAdapter.truncatedFormalJet a c T) =
        MultivariateFormalJet.formalJet a c := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | inl r =>
      simp only [AlgHom.comp_apply, truncatedFormalJet_Y, MultivariateFormalJet.formalJet_Y,
        map_mul, map_add, map_one, shiftMap_C, shiftMap_X_inl]
    | inr i =>
      simp only [AlgHom.comp_apply, truncatedFormalJet_X, MultivariateFormalJet.formalJet_X,
        map_add, map_sum, map_mul, shiftMap_C, shiftMap_X_inr, shiftMap_toMvPowerSeries]
      simp only [add_assoc]
      rw [← Finset.sum_add_distrib]
      congr 2
      apply Finset.sum_congr rfl
      intro r _
      simp only [logarithmicTails, map_mul, PowerSeries.toMvPowerSeries_C,
        FormalLogTruncation.logTail, map_sub, MultivariateFormalJet.formalLog]
      ring
  exact DFunLike.congr_fun he P

theorem formalJet_mem_weighted_of_mem_pow
    (a : Fin m → Fin k → ℤ) (c : Fin k ⊕ Fin m → ℂ)
    (hc : ∀ r, c (Sum.inl r) ≠ 0) (T : Fin m → Fin k → ℕ)
    (e : Fin k ⊕ Fin m → ℕ) (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 ≤ v j)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r))
    (R : ℚ) (he : ∀ j, R ≤ (e j : ℚ) * v j) (n : ℕ)
    (P : MvPolynomial (Fin k ⊕ Fin m) ℂ)
    (hP : P ∈ MultivariateLogPolynomialAdapter.logPowerIdeal a c T e ^ n) :
    MultivariateFormalJet.formalJet a c P ∈ rationalWeightedIdeal v hv (n * R) := by
  rw [← shiftMap_truncatedFormalJet a c T P]
  exact shiftMap_mem_rationalWeightedIdeal _ _ v hv (logarithmicTails_mem a T v hv hT)
    _ _ (MultivariateLogPolynomialAdapter.truncatedFormalJet_mem_weighted_of_mem_pow
      a c hc T e v hv R he n P hP)

theorem formalLog_packets_surjective_iff_truncated {α J : Type*}
    (a : Fin m → Fin k → ℤ) (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 ≤ v j) (H : ℚ)
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) ≤ (T i r : ℚ) * v (Sum.inl r))
    (c : J → Fin k ⊕ Fin m → ℂ) (P : α → MvPolynomial (Fin k ⊕ Fin m) ℂ) :
    Function.Surjective (fun b j => rationalCoefficientPacket v H
      (MultivariateFormalJet.formalJet a (c j) (P b))) ↔
    Function.Surjective (fun b j => rationalCoefficientPacket v H
      (MultivariateLogPolynomialAdapter.truncatedFormalJet a (c j) T (P b))) := by
  let tail := logarithmicTails a T
  let ht := logarithmicTails_constantCoeff a T
  let E := shiftEquiv tail ht
  have hw := logarithmicTails_mem a T v hv hT
  have he : ∀ f ∈ rationalWeightedIdeal v hv H, E f ∈ rationalWeightedIdeal v hv H :=
    fun f hf => (shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ rationalWeightedIdeal v hv H, E.symm f ∈ rationalWeightedIdeal v hv H := by
    intro f hf
    apply (shiftEquiv_mem_iff tail ht v hv hw H (E.symm f)).mp
    change E (E.symm f) ∈ rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hf
  have hh := FormalLogTruncation.packets_surjective_comp_equiv_iff v hv H E he hi
    (fun b j => MultivariateLogPolynomialAdapter.truncatedFormalJet a (c j) T (P b))
  simpa only [E, tail, ht, shiftEquiv_apply, shiftMap_truncatedFormalJet] using hh

end
end GeneralizedLogarithms.MultivariateFormalLogShift

/-- info: 'GeneralizedLogarithms.MultivariateFormalLogShift.shiftEquiv_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFormalLogShift.shiftEquiv_mem_iff

/-- info: 'GeneralizedLogarithms.MultivariateFormalLogShift.shiftMap_truncatedFormalJet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFormalLogShift.shiftMap_truncatedFormalJet

/-- info: 'GeneralizedLogarithms.MultivariateFormalLogShift.formalJet_mem_weighted_of_mem_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFormalLogShift.formalJet_mem_weighted_of_mem_pow

/-- info: 'GeneralizedLogarithms.MultivariateFormalLogShift.formalLog_packets_surjective_iff_truncated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFormalLogShift.formalLog_packets_surjective_iff_truncated
