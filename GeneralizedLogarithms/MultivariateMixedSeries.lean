import GeneralizedLogarithms.MultivariateFormalJet
import LogIrrationalityMeasure.Approximation.RowTranslation

/-!
# Separating transverse polynomial variables from longitudinal series

The coefficient identity below connects polynomial row translation over a
multivariate series ring with the actual series in all jet variables.
-/

namespace GeneralizedLogarithms.MultivariateMixedSeries

noncomputable section
open scoped BigOperators
open Finset.HasAntidiagonal

variable {σ τ R : Type*} [CommSemiring R]

def leftIndex (d : σ ⊕ τ →₀ ℕ) : σ →₀ ℕ :=
  d.comapDomain Sum.inl Sum.inl_injective.injOn

def rightIndex (d : σ ⊕ τ →₀ ℕ) : τ →₀ ℕ :=
  d.comapDomain Sum.inr Sum.inr_injective.injOn

@[simp] theorem left_zero : leftIndex (0 : σ ⊕ τ →₀ ℕ) = 0 := by ext; rfl
@[simp] theorem right_zero : rightIndex (0 : σ ⊕ τ →₀ ℕ) = 0 := by ext; rfl

@[simp] theorem left_sumElim (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    leftIndex (a.sumElim b) = a := Finsupp.comapDomain_inl_sumElim a b

@[simp] theorem right_sumElim (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    rightIndex (a.sumElim b) = b := Finsupp.comapDomain_inr_sumElim a b

theorem sumElim_indices (d : σ ⊕ τ →₀ ℕ) :
    (leftIndex d).sumElim (rightIndex d) = d := Finsupp.comapDomain_sumElim_comapDomain d

def embedFun (P : MvPolynomial τ (MvPowerSeries σ R)) : MvPowerSeries (σ ⊕ τ) R :=
  fun d => MvPowerSeries.coeff (leftIndex d) (P.coeff (rightIndex d))

@[simp] theorem coeff_embedFun (P : MvPolynomial τ (MvPowerSeries σ R))
    (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    MvPowerSeries.coeff (a.sumElim b) (embedFun P) =
      MvPowerSeries.coeff a (P.coeff b) := by
  change MvPowerSeries.coeff (leftIndex (a.sumElim b)) (P.coeff (rightIndex (a.sumElim b))) = _
  simp only [left_sumElim, right_sumElim]

theorem embedFun_mul (P Q : MvPolynomial τ (MvPowerSeries σ R)) :
    embedFun (P * Q) = embedFun P * embedFun Q := by
  classical
  ext d
  obtain ⟨⟨a, b⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective d
  change MvPowerSeries.coeff (a.sumElim b) _ = MvPowerSeries.coeff (a.sumElim b) _
  rw [coeff_embedFun, MvPolynomial.coeff_mul, map_sum, MvPowerSeries.coeff_mul,
    ← Finsupp.image_sumElim_product_antidiagonal, Finset.sum_image]
  · simp only [coeff_embedFun, MvPowerSeries.coeff_mul, Finset.sum_product]
    rw [Finset.sum_comm]
  · rintro ⟨⟨a₁, a₂⟩, b₁, b₂⟩ _ ⟨⟨c₁, c₂⟩, e₁, e₂⟩ _ he
    have h₁ := congrArg (fun q => leftIndex q.1) he
    have h₂ := congrArg (fun q => leftIndex q.2) he
    have h₃ := congrArg (fun q => rightIndex q.1) he
    have h₄ := congrArg (fun q => rightIndex q.2) he
    simp only [left_sumElim, right_sumElim] at h₁ h₂ h₃ h₄
    simp_all

def embed : MvPolynomial τ (MvPowerSeries σ R) →+* MvPowerSeries (σ ⊕ τ) R where
  toFun := embedFun
  map_zero' := by
    ext d
    change MvPowerSeries.coeff (leftIndex d) ((0 : MvPolynomial τ (MvPowerSeries σ R)).coeff (rightIndex d)) = 0
    simp
  map_one' := by
    classical
    ext d
    obtain ⟨⟨a, b⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective d
    change MvPowerSeries.coeff (a.sumElim b) _ = MvPowerSeries.coeff (a.sumElim b) _
    rw [coeff_embedFun]
    change MvPowerSeries.coeff a ((1 : MvPolynomial τ (MvPowerSeries σ R)).coeff b) =
      MvPowerSeries.coeff (a.sumElim b) (1 : MvPowerSeries (σ ⊕ τ) R)
    have he : a.sumElim b = 0 ↔ a = 0 ∧ b = 0 := by
      constructor
      · intro h; exact ⟨by simpa using congrArg leftIndex h, by simpa using congrArg rightIndex h⟩
      · rintro ⟨rfl, rfl⟩; simp
    simp only [MvPolynomial.coeff_one, MvPowerSeries.coeff_one, he]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
      simp [MvPowerSeries.coeff_one, ha, hb, eq_comm]
  map_add' P Q := by
    ext d
    change MvPowerSeries.coeff (leftIndex d) ((P + Q).coeff (rightIndex d)) =
      MvPowerSeries.coeff (leftIndex d) (P.coeff (rightIndex d)) +
        MvPowerSeries.coeff (leftIndex d) (Q.coeff (rightIndex d))
    simp
  map_mul' := embedFun_mul

@[simp] theorem coeff_embed (P : MvPolynomial τ (MvPowerSeries σ R))
    (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    MvPowerSeries.coeff (a.sumElim b) (embed P) = MvPowerSeries.coeff a (P.coeff b) :=
  coeff_embedFun P a b

@[simp] theorem embed_C (f : MvPowerSeries σ R) :
    embed (MvPolynomial.C f : MvPolynomial τ _) =
      MvPowerSeries.rename (Function.Embedding.inl : σ ↪ σ ⊕ τ) f := by
  classical
  ext d
  obtain ⟨⟨a, b⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective d
  change MvPowerSeries.coeff (a.sumElim b) _ = MvPowerSeries.coeff (a.sumElim b) _
  rw [coeff_embed]
  by_cases hb : b = 0
  · subst b
    rw [MvPolynomial.coeff_C, if_pos rfl, ← Finsupp.embDomain_inl]
    exact (MvPowerSeries.coeff_embDomain_rename Function.Embedding.inl f a).symm
  · rw [MvPolynomial.coeff_C, ite_eq_right (Ne.symm hb), map_zero]
    symm
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨e, he⟩
    apply hb
    change Finsupp.mapDomain (Function.Embedding.inl : σ ↪ σ ⊕ τ) e = a.sumElim b at he
    rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_inl] at he
    simpa only [right_sumElim] using (congrArg rightIndex he).symm

@[simp] theorem embed_X (i : τ) :
    embed (MvPolynomial.X i : MvPolynomial τ (MvPowerSeries σ R)) = MvPowerSeries.X (Sum.inr i) := by
  classical
  ext d
  obtain ⟨⟨a, b⟩, rfl⟩ := Finsupp.sumFinsuppEquivProdFinsupp.symm.surjective d
  change MvPowerSeries.coeff (a.sumElim b) _ = MvPowerSeries.coeff (a.sumElim b) _
  rw [coeff_embed]
  have he : a.sumElim b = Finsupp.single (Sum.inr i) 1 ↔ a = 0 ∧ b = Finsupp.single i 1 := by
    constructor
    · intro h
      have h' : a.sumElim b = (0 : σ →₀ ℕ).sumElim (Finsupp.single i 1) := by simpa using h
      exact ⟨by simpa only [left_sumElim] using congrArg leftIndex h',
        by simpa only [right_sumElim] using congrArg rightIndex h'⟩
    · rintro ⟨rfl, rfl⟩; exact Finsupp.sumElim_zero_single i 1
  simp only [MvPolynomial.coeff_X, MvPowerSeries.coeff_X, he]
  by_cases ha : a = 0 <;> by_cases hb : b = Finsupp.single i 1 <;>
    simp [MvPowerSeries.coeff_one, ha, hb, eq_comm]

end
end GeneralizedLogarithms.MultivariateMixedSeries

/-- info: 'GeneralizedLogarithms.MultivariateMixedSeries.coeff_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateMixedSeries.coeff_embed

/-- info: 'GeneralizedLogarithms.MultivariateMixedSeries.embed_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateMixedSeries.embed_C
