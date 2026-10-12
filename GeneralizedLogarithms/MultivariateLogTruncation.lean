import GeneralizedLogarithms.MultilogBranchCoordinates
import LogIrrationalityMeasure.Analysis.FormalLogTailOrder

/-!
# Truncating several logarithms preserves branch contact

Each transverse coordinate receives a finite sum of scaled logarithm tails.
Terms with zero integer coefficient require no cutoff bound. Every contributing
tail has order strictly above the contact threshold, as does their finite sum.
The generic high-tail contact theorem therefore identifies the genuine and
polynomially truncated branch contacts.
-/

namespace GeneralizedLogarithms.MultivariateLogTruncation

noncomputable section

open scoped BigOperators
open LogIrrationalityMeasure.LogExponent
open FormalLogTruncation MultilogBranchCoordinates

section Orders

theorem order_add_strict_lower (B : ℚ) (f g : PowerSeries ℂ)
    (hf : ∀ n : ℕ, f.order = (n : ℕ∞) → B < (n : ℚ))
    (hg : ∀ n : ℕ, g.order = (n : ℕ∞) → B < (n : ℚ))
    (n : ℕ) (hn : (f + g).order = (n : ℕ∞)) : B < (n : ℚ) := by
  have hmin : min f.order g.order ≤ (n : ℕ∞) :=
    (PowerSeries.min_order_le_order_add f g).trans hn.le
  rcases min_le_iff.mp hmin with h | h
  · have hnontop : f.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    have he := ENat.natCast_toNat hnontop
    have hb := hf f.order.toNat he.symm
    have hnat : f.order.toNat ≤ n := by exact_mod_cast he.symm ▸ h
    exact hb.trans_le (by exact_mod_cast hnat)
  · have hnontop : g.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    have he := ENat.natCast_toNat hnontop
    have hb := hg g.order.toNat he.symm
    have hnat : g.order.toNat ≤ n := by exact_mod_cast he.symm ▸ h
    exact hb.trans_le (by exact_mod_cast hnat)

theorem order_finset_sum_strict_lower {ι : Type*} (B : ℚ) (s : Finset ι)
    (f : ι → PowerSeries ℂ)
    (hf : ∀ i ∈ s, ∀ n : ℕ, (f i).order = (n : ℕ∞) → B < (n : ℚ)) :
    ∀ n : ℕ, (∑ i ∈ s, f i).order = (n : ℕ∞) → B < (n : ℚ) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n hn; simp at hn
  | @insert i s his ih =>
    rw [Finset.sum_insert his]
    exact order_add_strict_lower B (f i) (∑ j ∈ s, f j)
      (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem order_mul_left_strict_lower (B : ℚ) (g f : PowerSeries ℂ)
    (hf : ∀ n : ℕ, f.order = (n : ℕ∞) → B < (n : ℚ))
    (n : ℕ) (hn : (g * f).order = (n : ℕ∞)) : B < (n : ℚ) := by
  have h : f.order ≤ (n : ℕ∞) := by
    calc
      f.order ≤ g.order + f.order := le_add_of_nonneg_left (by simp)
      _ ≤ (g * f).order := PowerSeries.le_order_mul g f
      _ = _ := hn
  have hnontop : f.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
  have he := ENat.natCast_toNat hnontop
  have hb := hf f.order.toNat he.symm
  have hnat : f.order.toNat ≤ n := by exact_mod_cast he.symm ▸ h
  exact hb.trans_le (by exact_mod_cast hnat)

/-- A logarithm tail in any one source coordinate is above any smaller
weighted target threshold. -/
theorem composed_logTail_strict_contact {ι : Type*} [Fintype ι]
    (v : ι → ℚ) (hv : ∀ i, 0 < v i) (b : ι → PowerSeries ℂ)
    (hne : ∃ i, b i ≠ 0) (hb : ∀ i, PowerSeries.constantCoeff (b i) = 0)
    (source target : ι) (T : ℕ) (hT : v target < (T : ℚ) * v source)
    (n : ℕ) (hn : PowerSeries.order (PowerSeries.subst (b source) (logTail T)) = (n : ℕ∞)) :
    BranchContact.contact v b hne * v target < (n : ℚ) := by
  have hTpos : 0 < T := by
    by_contra h
    have hz : T = 0 := by omega
    rw [hz, Nat.cast_zero, zero_mul] at hT
    exact (not_lt_of_ge (hv target).le) hT
  have horder := FormalBranchContact.composed_logTail_order_ge T (b source) (hb source)
  rw [hn] at horder
  have hfinite : (b source).order ≠ ⊤ := by
    intro htop
    have hT0 : (T : ℕ∞) ≠ 0 := by exact_mod_cast hTpos.ne'
    simp only [htop, ENat.mul_top hT0] at horder
    simp at horder
  obtain ⟨q, hq⟩ := ENat.ne_top_iff_exists.mp hfinite
  rw [← hq] at horder
  have hnat : T * q ≤ n := by exact_mod_cast horder
  have hcontact := BranchContact.contact_bound v hv b hne source q hq.symm
  have hμ := BranchContact.contact_pos v hv b hne hb
  calc
    BranchContact.contact v b hne * v target <
        BranchContact.contact v b hne * ((T : ℚ) * v source) :=
      mul_lt_mul_of_pos_left hT hμ
    _ = (T : ℚ) * (BranchContact.contact v b hne * v source) := by ring
    _ ≤ (T : ℚ) * (q : ℚ) := mul_le_mul_of_nonneg_left hcontact (by positivity)
    _ ≤ (n : ℚ) := by exact_mod_cast hnat

end Orders

variable {k m : ℕ}

/-- The combined error, with its coefficient and individual cutoff tracked. -/
def composedLogTails (a : Fin m → Fin k → ℤ)
    (b : (Fin k ⊕ Fin m) → PowerSeries ℂ) (T : Fin m → Fin k → ℕ) :
    (Fin k ⊕ Fin m) → PowerSeries ℂ :=
  Sum.elim (fun _ => 0) (fun i => ∑ r, PowerSeries.C (a i r : ℂ) *
    PowerSeries.subst (b (Sum.inl r)) (logTail (T i r)))

def truncatedBranchCoordinates (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (T : Fin m → Fin k → ℕ) : (Fin k ⊕ Fin m) → PowerSeries ℂ :=
  Sum.elim (fun r => centeredY (cY r) (y r))
    (fun i => x i - PowerSeries.C (cX i) - ∑ r, PowerSeries.C (a i r : ℂ) *
      PowerSeries.subst (centeredY (cY r) (y r))
        (PowerSeries.trunc (T i r) (PowerSeries.log ℂ) : PowerSeries ℂ))

theorem truncatedBranchCoordinates_eq_add_tail (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (T : Fin m → Fin k → ℕ) (hy : ∀ r, PowerSeries.constantCoeff (y r) = cY r) :
    truncatedBranchCoordinates a cY cX y x T = fun j =>
      branchCoordinates a cY cX y x j + composedLogTails a (branchCoordinates a cY cX y x) T j := by
  have hs (r : Fin k) := PowerSeries.HasSubst.of_constantCoeff_zero'
    (constantCoeff_centeredY (cY r) (hcY r) (y r) (hy r))
  funext j
  cases j with
  | inl r => simp [truncatedBranchCoordinates, branchCoordinates, composedLogTails]
  | inr i =>
    have htail (r : Fin k) : PowerSeries.subst (centeredY (cY r) (y r)) (logTail (T i r)) =
        PowerSeries.subst (centeredY (cY r) (y r)) (PowerSeries.log ℂ) -
          PowerSeries.subst (centeredY (cY r) (y r))
            (PowerSeries.trunc (T i r) (PowerSeries.log ℂ) : PowerSeries ℂ) :=
      PowerSeries.subst_sub (hs r) _ _
    simp only [truncatedBranchCoordinates, branchCoordinates, composedLogTails,
      Sum.elim_inl, Sum.elim_inr, htail, mul_sub, Finset.sum_sub_distrib]
    ring

theorem composedLogTails_strict_contact
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j) (a : Fin m → Fin k → ℤ)
    (b : (Fin k ⊕ Fin m) → PowerSeries ℂ) (hne : ∃ j, b j ≠ 0)
    (hb : ∀ j, PowerSeries.constantCoeff (b j) = 0) (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, a i r ≠ 0 → v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r)) :
    ∀ j (n : ℕ), (composedLogTails a b T j).order = (n : ℕ∞) →
      BranchContact.contact v b hne * v j < (n : ℚ) := by
  intro j
  cases j with
  | inl r => intro n hn; simp [composedLogTails] at hn
  | inr i =>
    dsimp only [composedLogTails, Sum.elim_inr]
    apply order_finset_sum_strict_lower
    intro r _ n hn
    by_cases ha : a i r = 0
    · simp [ha] at hn
    · exact order_mul_left_strict_lower _ _ _
        (composed_logTail_strict_contact v hv b hne hb (Sum.inl r) (Sum.inr i)
          (T i r) (hT i r ha)) n hn

theorem truncatedBranchCoordinates_not_all_zero_of_nonzero
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j) (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : ∀ r, PowerSeries.constantCoeff (y r) = cY r)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = cX i)
    (hne : ∃ j, branchCoordinates a cY cX y x j ≠ 0)
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, a i r ≠ 0 → v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r)) :
    ∃ j, truncatedBranchCoordinates a cY cX y x T j ≠ 0 := by
  rw [truncatedBranchCoordinates_eq_add_tail a cY cX hcY y x T hy]
  exact BranchContact.add_not_all_zero v hv _ _ hne
    (composedLogTails_strict_contact v hv a _ hne
      (branchCoordinates_centered a cY cX hcY y x hy hx) T hT)

theorem contact_truncatedBranchCoordinates_eq_of_nonzero
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j) (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : ∀ r, PowerSeries.constantCoeff (y r) = cY r)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = cX i)
    (hne : ∃ j, branchCoordinates a cY cX y x j ≠ 0)
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, a i r ≠ 0 → v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r)) :
    BranchContact.contact v (truncatedBranchCoordinates a cY cX y x T)
      (truncatedBranchCoordinates_not_all_zero_of_nonzero v hv a cY cX hcY y x hy hx hne T hT) =
        BranchContact.contact v (branchCoordinates a cY cX y x) hne := by
  have hh := BranchContact.contact_add_high_tail v hv
    (branchCoordinates a cY cX y x) (composedLogTails a (branchCoordinates a cY cX y x) T) hne
    (composedLogTails_strict_contact v hv a _ hne
      (branchCoordinates_centered a cY cX hcY y x hy hx) T hT)
  simpa only [← truncatedBranchCoordinates_eq_add_tail a cY cX hcY y x T hy] using hh

/-- Convenient form imposing the cutoff bound on every matrix entry. -/
theorem truncatedBranchCoordinates_not_all_zero
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j) (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : ∀ r, PowerSeries.constantCoeff (y r) = cY r)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = cX i)
    (hne : ∃ j, branchCoordinates a cY cX y x j ≠ 0)
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r)) :
    ∃ j, truncatedBranchCoordinates a cY cX y x T j ≠ 0 :=
  truncatedBranchCoordinates_not_all_zero_of_nonzero v hv a cY cX hcY y x hy hx hne T
    (fun i r _ => hT i r)

/-- The polynomially truncated coordinates have exactly the true multilog contact. -/
theorem contact_truncatedBranchCoordinates_eq
    (v : (Fin k ⊕ Fin m) → ℚ) (hv : ∀ j, 0 < v j) (a : Fin m → Fin k → ℤ)
    (cY : Fin k → ℂ) (cX : Fin m → ℂ) (hcY : ∀ r, cY r ≠ 0)
    (y : Fin k → PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : ∀ r, PowerSeries.constantCoeff (y r) = cY r)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = cX i)
    (hne : ∃ j, branchCoordinates a cY cX y x j ≠ 0)
    (T : Fin m → Fin k → ℕ)
    (hT : ∀ i r, v (Sum.inr i) < (T i r : ℚ) * v (Sum.inl r)) :
    BranchContact.contact v (truncatedBranchCoordinates a cY cX y x T)
      (truncatedBranchCoordinates_not_all_zero v hv a cY cX hcY y x hy hx hne T hT) =
        BranchContact.contact v (branchCoordinates a cY cX y x) hne :=
  contact_truncatedBranchCoordinates_eq_of_nonzero v hv a cY cX hcY y x hy hx hne T
    (fun i r _ => hT i r)

end
end GeneralizedLogarithms.MultivariateLogTruncation

/-- info: 'GeneralizedLogarithms.MultivariateLogTruncation.composedLogTails_strict_contact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogTruncation.composedLogTails_strict_contact

/-- info: 'GeneralizedLogarithms.MultivariateLogTruncation.contact_truncatedBranchCoordinates_eq_of_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogTruncation.contact_truncatedBranchCoordinates_eq_of_nonzero

/-- info: 'GeneralizedLogarithms.MultivariateLogTruncation.contact_truncatedBranchCoordinates_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateLogTruncation.contact_truncatedBranchCoordinates_eq
