import GeneralizedLogarithms.LongitudinalComparison
import LogIrrationalityMeasure.Approximation.WeightSeparationProducts

/-!
# Transverse weight separation with several longitudinal coordinates

The longitudinal coordinates all have normalized weight one. Only a largest
transverse discrepancy triggers separation; no inequality is imposed on two
sets which differ only in longitudinal coordinates.
-/

namespace GeneralizedLogarithms.TransverseWeightSeparation

noncomputable section

open scoped BigOperators

variable {k m : ℕ}

/-- Put all longitudinal coordinates first, followed by the transverse ones. -/
def coordinateIndex (k m : ℕ) : (Fin k ⊕ Fin m) ↪ ℕ where
  toFun := Sum.elim Fin.val (fun i => k + i.val)
  inj' := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Fin.ext hij)
      | inr j => simp only [Sum.elim_inl, Sum.elim_inr] at hij; omega
    | inr i =>
      cases j with
      | inl j => simp only [Sum.elim_inl, Sum.elim_inr] at hij; omega
      | inr j =>
        simp only [Sum.elim_inr] at hij
        exact congrArg Sum.inr (Fin.ext (by omega))

@[simp] theorem coordinateIndex_inl (r : Fin k) :
    coordinateIndex k m (Sum.inl r) = r.val := rfl

@[simp] theorem coordinateIndex_inr (i : Fin m) :
    coordinateIndex k m (Sum.inr i) = k + i.val := rfl

def separationFactor (n : ℕ) (C w₀ v₀ θ : ℝ) : ℝ :=
  C * (max 1 (max v₀ 1 / min w₀ θ)) ^ n

theorem separationFactor_pos (n : ℕ) (C w₀ v₀ θ : ℝ) (hC : 0 < C) :
    0 < separationFactor n C w₀ v₀ θ := by
  apply mul_pos hC
  exact pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _

/-- Uniform lower and upper bounds transfer normalized product separation to
the actual degree and jet weights. -/
theorem blockWeight_products_of_normalized
    [DecidableEq (Fin k ⊕ Fin m)]
    (C w₀ v₀ θ : ℝ) (hC : 0 < C) (hw₀ : 0 < w₀) (hv₀ : 0 < v₀)
    (hθ : 0 < θ) (x : ℕ → ℝ) (hxY : ∀ r : Fin k, x r.val = 1)
    (hx : ∀ j, 1 ≤ x j) (A B : Finset (Fin k ⊕ Fin m))
    (hcard : A.card = B.card)
    (hsep : separationFactor (k + m) C w₀ v₀ θ *
      (∏ j ∈ B, x (coordinateIndex k m j)) < ∏ j ∈ A, x (coordinateIndex k m j)) :
    C * (∏ j ∈ B, blockWeight (Finset.univ.image Sum.inr)
      (fun j => x (coordinateIndex k m j)) v₀ j) <
    ∏ j ∈ A, blockWeight (Finset.univ.image Sum.inr)
      (fun j => θ * x (coordinateIndex k m j)) w₀ j := by
  classical
  let L : ℝ := min w₀ θ
  let R : ℝ := max v₀ 1
  let T : ℝ := max 1 (R / L)
  have hL : 0 < L := lt_min hw₀ hθ
  have hR : 0 < R := lt_of_lt_of_le hv₀ (le_max_left _ _)
  have hT : 1 ≤ T := le_max_left _ _
  have hxpos (j : ℕ) : 0 < x j := zero_lt_one.trans_le (hx j)
  have hdegree (j : Fin k ⊕ Fin m) : L * x (coordinateIndex k m j) ≤
      blockWeight (Finset.univ.image Sum.inr)
        (fun j => θ * x (coordinateIndex k m j)) w₀ j := by
    cases j with
    | inl r => simpa [blockWeight, hxY, L] using min_le_left w₀ θ
    | inr i =>
      simpa [blockWeight, L] using
        mul_le_mul_of_nonneg_right (min_le_right w₀ θ) (hxpos (k + i.val)).le
  have hjet (j : Fin k ⊕ Fin m) :
      blockWeight (Finset.univ.image Sum.inr)
        (fun j => x (coordinateIndex k m j)) v₀ j ≤ R * x (coordinateIndex k m j) := by
    cases j with
    | inl r => simpa [blockWeight, hxY, R] using le_max_left v₀ 1
    | inr i =>
      simpa [blockWeight, R] using
        mul_le_mul_of_nonneg_right (le_max_right v₀ 1) (hxpos (k + i.val)).le
  have hjetnonneg (j : Fin k ⊕ Fin m) : 0 ≤
      blockWeight (Finset.univ.image Sum.inr)
        (fun j => x (coordinateIndex k m j)) v₀ j := by
    cases j with
    | inl r => simpa [blockWeight] using hv₀.le
    | inr i => simpa [blockWeight] using (hxpos (coordinateIndex k m (Sum.inr i))).le
  have hdegreeprod : L ^ A.card * (∏ j ∈ A, x (coordinateIndex k m j)) ≤
      ∏ j ∈ A, blockWeight (Finset.univ.image Sum.inr)
        (fun j => θ * x (coordinateIndex k m j)) w₀ j := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun j _ => mul_nonneg hL.le (hxpos _).le)
      (fun j _ => hdegree j)
  have hjetprod : (∏ j ∈ B, blockWeight (Finset.univ.image Sum.inr)
      (fun j => x (coordinateIndex k m j)) v₀ j) ≤
      R ^ B.card * (∏ j ∈ B, x (coordinateIndex k m j)) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun j _ => hjetnonneg j) (fun j _ => hjet j)
  have hbound : B.card ≤ k + m := by
    simpa using Finset.card_le_univ B
  have hRle : R ≤ T * L := (div_le_iff₀ hL).mp (le_max_right _ _)
  have hpowers : R ^ B.card ≤ T ^ (k + m) * L ^ B.card := by
    calc
      _ ≤ (T * L) ^ B.card := pow_le_pow_left₀ hR.le hRle _
      _ = T ^ B.card * L ^ B.card := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT hbound)
        (pow_nonneg hL.le _)
  calc
    _ ≤ C * (R ^ B.card * (∏ j ∈ B, x (coordinateIndex k m j))) :=
      mul_le_mul_of_nonneg_left hjetprod hC.le
    _ ≤ C * ((T ^ (k + m) * L ^ B.card) *
        (∏ j ∈ B, x (coordinateIndex k m j))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpowers (Finset.prod_nonneg (fun j _ => (hxpos _).le))) hC.le
    _ = L ^ A.card * (separationFactor (k + m) C w₀ v₀ θ *
        (∏ j ∈ B, x (coordinateIndex k m j))) := by
      rw [hcard]
      change C * ((T ^ (k + m) * L ^ B.card) * _) =
        L ^ B.card * ((C * T ^ (k + m)) * _)
      ring
    _ < L ^ A.card * (∏ j ∈ A, x (coordinateIndex k m j)) :=
      mul_lt_mul_of_pos_left hsep (pow_pos hL _)
    _ ≤ _ := hdegreeprod

/-- Recursive growth is needed only at transverse indices. The longitudinal
normalized weights may all equal one. -/
theorem blockWeight_products_separated
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (horder : ∀ i j : Fin m, i < j → frameOrder.lt (Sum.inr i) (Sum.inr j))
    (C w₀ v₀ θ : ℝ) (hC : 0 < C) (hw₀ : 0 < w₀) (hv₀ : 0 < v₀)
    (hθ : 0 < θ) (x : ℕ → ℝ) (hxY : ∀ r : Fin k, x r.val = 1)
    (hx : ∀ j, 1 ≤ x j)
    (hgrowth : ∀ i : Fin m, separationFactor (k + m) C w₀ v₀ θ *
      (∏ j ∈ Finset.range (k + i.val), x j) < x (k + i.val))
    (A B : Finset (Fin k ⊕ Fin m)) (hcard : A.card = B.card)
    (i : Fin m) (hiA : Sum.inr i ∈ A) (hiB : Sum.inr i ∉ B)
    (hhigh : ∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
      (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) :
    C * (∏ j ∈ B, blockWeight (Finset.univ.image Sum.inr)
      (fun j => x (coordinateIndex k m j)) v₀ j) <
    ∏ j ∈ A, blockWeight (Finset.univ.image Sum.inr)
      (fun j => θ * x (coordinateIndex k m j)) w₀ j := by
  classical
  apply blockWeight_products_of_normalized C w₀ v₀ θ hC hw₀ hv₀ hθ x hxY hx A B hcard
  have hbelow : ∀ j ∈ B \ A, coordinateIndex k m j < k + i.val := by
    intro j hj
    obtain ⟨hjB, hjA⟩ := Finset.mem_sdiff.mp hj
    cases j with
    | inl r => change r.val < k + i.val; omega
    | inr j =>
      change k + j.val < k + i.val
      have hji : j ≠ i := by intro he; subst j; exact hiB hjB
      have hnot : ¬ i < j := fun hij => hjA ((hhigh j (horder i j hij)).mpr hjB)
      have hlt : j < i := lt_of_le_of_ne (le_of_not_gt hnot) hji
      exact Nat.add_lt_add_left hlt k
  have hsep := LogIrrationalityMeasure.LogExponent.normalized_products_separated x
    (separationFactor (k + m) C w₀ v₀ θ) hx
    (separationFactor_pos (k + m) C w₀ v₀ θ hC)
    (A.map (coordinateIndex k m)) (B.map (coordinateIndex k m)) (k + i.val)
    (by exact Finset.mem_map.mpr ⟨Sum.inr i, hiA, rfl⟩)
    (by
      intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
      have he : j = Sum.inr i := (coordinateIndex k m).injective hji
      exact hiB (he ▸ hj))
    (by
      intro j hj
      obtain ⟨hjB, hjA⟩ := Finset.mem_sdiff.mp hj
      obtain ⟨q, hqB, rfl⟩ := Finset.mem_map.mp hjB
      have hqA : q ∉ A := fun hq => hjA (Finset.mem_map.mpr ⟨q, hq, rfl⟩)
      exact hbelow q (Finset.mem_sdiff.mpr ⟨hqB, hqA⟩))
    (hgrowth i)
  simpa only [Finset.prod_map] using hsep

/-- One ambient-dimension bound can be used for transverse separation while
the codimension-dependent constant remains in the resulting inequality. -/
theorem rectangular_blockWeight_products_separated
    [frameOrder : LinearOrder (Fin k ⊕ Fin m)]
    (horder : ∀ i j : Fin m, i < j → frameOrder.lt (Sum.inr i) (Sum.inr j))
    (hn : 1 ≤ k + m) (epsilon w₀ v₀ θ : ℝ) (hepsilon : 0 < epsilon)
    (hw₀ : 0 < w₀) (hv₀ : 0 < v₀) (hθ : 0 < θ)
    (x : ℕ → ℝ) (hxY : ∀ r : Fin k, x r.val = 1) (hx : ∀ j, 1 ≤ x j)
    (hgrowth : ∀ i : Fin m,
      separationFactor (k + m)
        (((k + m : ℕ) : ℝ) ^ (k + m) * (1 + 1 / epsilon) ^ (k + m)) w₀ v₀ θ *
          (∏ j ∈ Finset.range (k + i.val), x j) < x (k + i.val))
    (A B : Finset (Fin k ⊕ Fin m)) (hcard : A.card = B.card)
    (i : Fin m) (hiA : Sum.inr i ∈ A) (hiB : Sum.inr i ∉ B)
    (hhigh : ∀ j : Fin m, frameOrder.lt (Sum.inr i) (Sum.inr j) →
      (Sum.inr j ∈ A ↔ Sum.inr j ∈ B)) :
    ((A.card : ℝ) ^ A.card / epsilon ^ A.card) *
        (∏ j ∈ B, blockWeight (Finset.univ.image Sum.inr)
          (fun j => x (coordinateIndex k m j)) v₀ j) <
      ∏ j ∈ A, blockWeight (Finset.univ.image Sum.inr)
        (fun j => θ * x (coordinateIndex k m j)) w₀ j := by
  classical
  let C : ℝ := ((k + m : ℕ) : ℝ) ^ (k + m) * (1 + 1 / epsilon) ^ (k + m)
  have hnR : (0 : ℝ) < (k + m : ℕ) := by exact_mod_cast (by omega : 0 < k + m)
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : A.card ≤ k + m := by simpa using Finset.card_le_univ A
  have hconstant : (A.card : ℝ) ^ A.card / epsilon ^ A.card ≤ C := by
    simpa [C, div_pow, div_eq_mul_inv] using
      rectangular_factor_le_fixed_degree A.card (k + m) 1 epsilon hn hbound
        zero_le_one hepsilon
  have hprod : 0 ≤ ∏ j ∈ B, blockWeight (Finset.univ.image Sum.inr)
      (fun j => x (coordinateIndex k m j)) v₀ j := by
    apply Finset.prod_nonneg
    intro j _
    cases j with
    | inl r => simpa [blockWeight] using hv₀.le
    | inr i => simpa [blockWeight] using zero_le_one.trans (hx (coordinateIndex k m (Sum.inr i)))
  exact (mul_le_mul_of_nonneg_right hconstant hprod).trans_lt
    (blockWeight_products_separated horder C w₀ v₀ θ hC hw₀ hv₀ hθ x hxY hx
      (by simpa [C] using hgrowth) A B hcard i hiA hiB hhigh)

end
end GeneralizedLogarithms.TransverseWeightSeparation

/-- info: 'GeneralizedLogarithms.TransverseWeightSeparation.blockWeight_products_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.TransverseWeightSeparation.blockWeight_products_separated

/-- info: 'GeneralizedLogarithms.TransverseWeightSeparation.rectangular_blockWeight_products_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.TransverseWeightSeparation.rectangular_blockWeight_products_separated
