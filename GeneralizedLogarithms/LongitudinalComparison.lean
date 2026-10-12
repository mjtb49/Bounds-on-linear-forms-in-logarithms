import GeneralizedLogarithms.NormalBasisRigidity

/-!
# Canceling common transverse weights

Once coordinate and frame normal bases have the same transverse intersection,
their universal multiplicity comparison gives the longitudinal inequality.
All geometric hypotheses enter through that comparison; no curve inequality or
parameter-existence result is asserted here.
-/

namespace GeneralizedLogarithms

open scoped BigOperators

section Weights

variable {ι : Type*} [DecidableEq ι]

/-- A common longitudinal weight outside the transverse set. -/
def blockWeight (X : Finset ι) (transverse : ι → ℝ) (longitudinal : ℝ) (i : ι) : ℝ :=
  if i ∈ X then transverse i else longitudinal

theorem prod_blockWeight (A X : Finset ι) (t : ι → ℝ) (L : ℝ) :
    (∏ i ∈ A, blockWeight X t L i) =
      (∏ i ∈ A ∩ X, t i) * L ^ (A \ X).card := by
  have hi : (∏ i ∈ A ∩ X, blockWeight X t L i) = ∏ i ∈ A ∩ X, t i := by
    apply Finset.prod_congr rfl
    intro i hi
    exact if_pos (Finset.mem_inter.mp hi).2
  have hy : (∏ i ∈ A \ X, blockWeight X t L i) = L ^ (A \ X).card := by
    calc
      _ = ∏ _i ∈ A \ X, L := by
        apply Finset.prod_congr rfl
        intro i hi
        exact if_neg (Finset.mem_sdiff.mp hi).2
      _ = _ := by simp
  calc
    _ = (∏ i ∈ A ∩ X, blockWeight X t L i) *
        ∏ i ∈ A \ X, blockWeight X t L i :=
      (Finset.prod_inter_mul_prod_sdiff A X _).symm
    _ = _ := by rw [hi, hy]

/-- The transverse factors cancel even when the two normal bases use different
longitudinal indices. Equal basis cardinality makes their longitudinal counts
equal; the remaining constant is still indexed by the actual codimension. -/
theorem longitudinal_bound_of_product_comparison
    (A B X I : Finset ι) (t : ι → ℝ) (θ w₀ v₀ : ℝ) (C : ℕ → ℝ)
    (hAX : A ∩ X = I) (hBX : B ∩ X = I) (hcard : A.card = B.card)
    (ht : ∀ i ∈ I, 0 < t i) (hv₀ : 0 < v₀)
    (hcomparison : (∏ i ∈ A, blockWeight X (fun j => θ * t j) w₀ i) ≤
      C A.card * ∏ i ∈ B, blockWeight X t v₀ i) :
    θ ^ I.card * (w₀ / v₀) ^ (A.card - I.card) ≤ C A.card := by
  have hAcount := Finset.card_sdiff_add_card_inter A X
  have hBcount := Finset.card_sdiff_add_card_inter B X
  rw [hAX] at hAcount
  rw [hBX] at hBcount
  have hAd : (A \ X).card = A.card - I.card := by omega
  have hBd : (B \ X).card = A.card - I.card := by omega
  rw [prod_blockWeight, prod_blockWeight, hAX, hBX, hAd, hBd,
    Finset.prod_mul_distrib, Finset.prod_const] at hcomparison
  have hP : 0 < ∏ i ∈ I, t i := Finset.prod_pos ht
  have hbase : θ ^ I.card * w₀ ^ (A.card - I.card) ≤
      C A.card * v₀ ^ (A.card - I.card) := by
    apply (mul_le_mul_iff_right₀ hP).mp
    convert hcomparison using 1 <;> ring
  rw [div_pow, ← mul_div_assoc]
  exact (div_le_iff₀ (pow_pos hv₀ _)).mpr hbase

/-- A strict longitudinal parameter inequality excludes the product comparison. -/
theorem not_product_comparison_of_longitudinal_gap
    (A B X I : Finset ι) (t : ι → ℝ) (θ w₀ v₀ : ℝ) (C : ℕ → ℝ)
    (hAX : A ∩ X = I) (hBX : B ∩ X = I) (hcard : A.card = B.card)
    (ht : ∀ i ∈ I, 0 < t i) (hv₀ : 0 < v₀)
    (hgap : C A.card < θ ^ I.card * (w₀ / v₀) ^ (A.card - I.card)) :
    ¬ (∏ i ∈ A, blockWeight X (fun j => θ * t j) w₀ i) ≤
      C A.card * ∏ i ∈ B, blockWeight X t v₀ i := by
  intro h
  exact (not_lt_of_ge (longitudinal_bound_of_product_comparison
    A B X I t θ w₀ v₀ C hAX hBX hcard ht hv₀ h)) hgap

end Weights

/-- A greedy transverse basis and the remaining coordinate directions bound
the normal dimension. This derives the upper bound `c ≤ r+k` when the
complement of `X` consists of the `k` longitudinal indices. -/
theorem normal_dimension_le_greedy_card_add_longitudinal
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [LinearOrder ι] (u : ι → V)
    (hu : Submodule.span K (Set.range u) = ⊤) (X I : Finset ι)
    (hI : IsGreedyBasis (K := K) u X I) :
    Module.finrank K V ≤ I.card + (Finset.univ \ X).card := by
  obtain ⟨A, hA, hAX⟩ := exists_normalBasis_with_intersection u hu X I
    hI.1 hI.2.1 hI.span_eq
  have hd : (A \ X).card ≤ (Finset.univ \ X).card := by
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, (Finset.mem_sdiff.mp hj).2⟩
  have hc := Finset.card_sdiff_add_card_inter A X
  rw [hAX, hA.card_eq] at hc
  omega

/-- The small-transverse-rank case has positive longitudinal dimension at most
`k`, and codimension at most `2*k-1`. The geometric work is the strict lower
bound `r < c` and the spanning bound `c ≤ r+k`, supplied as explicit inputs. -/
theorem small_rank_dimension_range (k r c : ℕ)
    (hrk : r < k) (hrc : r < c) (hupper : c ≤ r + k) :
    1 ≤ c - r ∧ c - r ≤ k ∧ c ≤ 2 * k - 1 := by omega

/-- A uniform bound with degree controlled by a codimension cap `b`, rather
than by ambient dimension. Substituting `b = 2*k-1` keeps the degree fixed as
the number of transverse directions grows. -/
theorem rectangular_factor_le_fixed_degree (c b : ℕ) (L σ : ℝ)
    (hb : 1 ≤ b) (hcb : c ≤ b) (hL : 0 ≤ L) (hσ : 0 < σ) :
    (c : ℝ) ^ c * (L / σ) ^ c ≤
      (b : ℝ) ^ b * (1 + L / σ) ^ b := by
  have hbase : 0 ≤ L / σ := div_nonneg hL hσ.le
  have hcb' : (c : ℝ) ≤ b := by exact_mod_cast hcb
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hp : (c : ℝ) ^ c ≤ (b : ℝ) ^ b := by
    calc
      _ ≤ (b : ℝ) ^ c := pow_le_pow_left₀ (Nat.cast_nonneg c) hcb' c
      _ ≤ _ := pow_le_pow_right₀ hb' hcb
  have hq : (L / σ) ^ c ≤ (1 + L / σ) ^ b := by
    calc
      _ ≤ (1 + L / σ) ^ c :=
        pow_le_pow_left₀ hbase (by linarith) c
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hcb
  exact mul_le_mul hp hq (pow_nonneg hbase _) (pow_nonneg (Nat.cast_nonneg b) _)

end GeneralizedLogarithms

/-- info: 'GeneralizedLogarithms.longitudinal_bound_of_product_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.longitudinal_bound_of_product_comparison

/-- info: 'GeneralizedLogarithms.rectangular_factor_le_fixed_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.rectangular_factor_le_fixed_degree

/-- info: 'GeneralizedLogarithms.normal_dimension_le_greedy_card_add_longitudinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.normal_dimension_le_greedy_card_add_longitudinal
