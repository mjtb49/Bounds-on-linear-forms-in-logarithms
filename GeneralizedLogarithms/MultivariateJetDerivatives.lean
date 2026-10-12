import LogIrrationalityMeasure.Jets.FormalJetDerivatives
import LogIrrationalityMeasure.Jets.FormalBranchOrderRational

/-!
# Derivative budgets in multivariate logarithmic jet coordinates

The longitudinal jet operators are `(1 + T_r) ∂/∂T_r`; the transverse
operators are `∂/∂U_i`. Each lowers rational weighted vanishing by at most
its coordinate weight. A word therefore lowers it by at most its total cost.
The final theorem translates this proved membership into an order bound after
substitution along a branch with the specified contact orders.
-/

namespace GeneralizedLogarithms.MultivariateJetDerivatives

noncomputable section

open MvPowerSeries
open LogIrrationalityMeasure.LogExponent
open JetGeometry

variable {R : Type*} [CommRing R] {k m : ℕ}

/-- The multivariate logarithmic frame in formal jet coordinates. -/
def jetFrame (j : Fin k ⊕ Fin m) :
    Derivation R (MvPowerSeries (Fin k ⊕ Fin m) R)
      (MvPowerSeries (Fin k ⊕ Fin m) R) :=
  Sum.elim
    (fun r => (1 + X (Sum.inl r) : MvPowerSeries (Fin k ⊕ Fin m) R) •
      pderiv (Sum.inl r))
    (fun i => pderiv (Sum.inr i)) j

@[simp] theorem jetFrame_inl (r : Fin k) (f : MvPowerSeries (Fin k ⊕ Fin m) R) :
    jetFrame (Sum.inl r) f = (1 + X (Sum.inl r)) * pderiv (Sum.inl r) f := by
  simp only [jetFrame, Sum.elim_inl, Derivation.smul_apply, smul_eq_mul]

@[simp] theorem jetFrame_inr (i : Fin m) (f : MvPowerSeries (Fin k ⊕ Fin m) R) :
    jetFrame (Sum.inr i) f = pderiv (Sum.inr i) f := rfl

/-- A single frame derivative spends at most its coordinate weight. -/
theorem jetFrame_mem_rationalWeightedIdeal (v : Fin k ⊕ Fin m → ℚ)
    (hv : ∀ j, 0 ≤ v j) (H : ℚ) (f : MvPowerSeries (Fin k ⊕ Fin m) R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (j : Fin k ⊕ Fin m) :
    jetFrame j f ∈ rationalWeightedIdeal v hv (H - v j) := by
  cases j with
  | inl r =>
    rw [jetFrame_inl]
    exact FormalJetDerivatives.mul_pderiv_mem_rationalWeightedIdeal v hv H f
      (1 + X (Sum.inl r)) hf (Sum.inl r)
  | inr i =>
    rw [jetFrame_inr]
    exact FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal v hv H f hf (Sum.inr i)

/-- Apply the jet-frame derivatives in the listed order. -/
def jetFrameWord (word : List (Fin k ⊕ Fin m))
    (f : MvPowerSeries (Fin k ⊕ Fin m) R) : MvPowerSeries (Fin k ⊕ Fin m) R :=
  word.foldr (fun j g => jetFrame j g) f

@[simp] theorem jetFrameWord_nil (f : MvPowerSeries (Fin k ⊕ Fin m) R) :
    jetFrameWord [] f = f := rfl

@[simp] theorem jetFrameWord_cons (j : Fin k ⊕ Fin m) (word : List (Fin k ⊕ Fin m))
    (f : MvPowerSeries (Fin k ⊕ Fin m) R) :
    jetFrameWord (j :: word) f = jetFrame j (jetFrameWord word f) := rfl

theorem jetFrameWord_append (u v : List (Fin k ⊕ Fin m))
    (f : MvPowerSeries (Fin k ⊕ Fin m) R) :
    jetFrameWord (u ++ v) f = jetFrameWord u (jetFrameWord v f) := by
  induction u with
  | nil => rfl
  | cons j u ih => simp only [List.cons_append, jetFrameWord_cons, ih]

/-- The total loss of weighted vanishing is bounded by the word's total cost. -/
theorem jetFrameWord_mem_rationalWeightedIdeal (v : Fin k ⊕ Fin m → ℚ)
    (hv : ∀ j, 0 ≤ v j) (H : ℚ) (f : MvPowerSeries (Fin k ⊕ Fin m) R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (word : List (Fin k ⊕ Fin m)) :
    jetFrameWord word f ∈ rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  induction word with
  | nil => simpa only [jetFrameWord_nil, List.map_nil, List.sum_nil, sub_zero] using hf
  | cons j word ih =>
    have h := jetFrame_mem_rationalWeightedIdeal v hv (H - (word.map v).sum)
      (jetFrameWord word f) ih j
    simpa only [jetFrameWord_cons, List.map_cons, List.sum_cons, sub_sub, add_comm] using h

/-- After branch substitution, contact bounds turn the remaining weighted
vanishing into an actual power-series order lower bound. -/
theorem jetFrameWord_powerSeries_order_lower
    {S : Type*} [CommRing S] [Algebra R S]
    (v : Fin k ⊕ Fin m → ℚ) (hv : ∀ j, 0 ≤ v j)
    (μ H : ℚ) (hμ : 0 ≤ μ) (f : MvPowerSeries (Fin k ⊕ Fin m) R)
    (b : (Fin k ⊕ Fin m) → PowerSeries S) (hb : HasSubst b)
    (hf : f ∈ rationalWeightedIdeal v hv H)
    (hcontact : ∀ j (n : ℕ), (b j).order = (n : ℕ∞) → μ * v j ≤ (n : ℚ))
    (word : List (Fin k ⊕ Fin m)) :
    (⌈μ * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      PowerSeries.order ((jetFrameWord word f).subst b) :=
  FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv μ (H - (word.map v).sum) hμ (jetFrameWord word f) b hb
    (jetFrameWord_mem_rationalWeightedIdeal v hv H f hf word) hcontact

end
end GeneralizedLogarithms.MultivariateJetDerivatives

/-- info: 'GeneralizedLogarithms.MultivariateJetDerivatives.jetFrame_mem_rationalWeightedIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateJetDerivatives.jetFrame_mem_rationalWeightedIdeal

/-- info: 'GeneralizedLogarithms.MultivariateJetDerivatives.jetFrameWord_mem_rationalWeightedIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateJetDerivatives.jetFrameWord_mem_rationalWeightedIdeal

/-- info: 'GeneralizedLogarithms.MultivariateJetDerivatives.jetFrameWord_powerSeries_order_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateJetDerivatives.jetFrameWord_powerSeries_order_lower
