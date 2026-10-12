import GeneralizedLogarithms.MultivariateModeCapacity
import LogIrrationalityMeasure.Analysis.CollisionLimit

/-!
# Infinite determinant bounds from multivariate mode capacity

Finite multilinearity groups coefficient rows before testing collisions.
A uniform bound for every finite truncation passes to the determinant limit.
The final theorem uses the complete mode `(group, Taylor multi-index)` and
retains half the geometric decay for summation. Actual analytic row identities
and coefficient estimates remain inputs to this general analytic lemma.
-/

namespace GeneralizedLogarithms.MultivariateInfiniteCollision

noncomputable section
open scoped BigOperators Topology
open Filter
open LogIrrationalityMeasure.LogExponent

section Finite
variable {ι Γ δ : Type*} [Fintype ι] [DecidableEq ι] [Fintype δ]

theorem finite_degree_saving_bound
    (group : ι → Γ) (B : ι → δ → ℂ) (C : Γ → δ → ι → ℂ)
    (degree : δ → ℕ) (D s saving Z : ℝ) (L : ι → ℝ)
    (hD : 0 ≤ D) (hs0 : 0 < s) (hs1 : s < 1) (hZ : 0 ≤ Z) (hL : ∀ i, 0 ≤ L i)
    (hC : ∀ g d j, ‖C g d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ degree d)
    (hsave : ∀ f : ι → δ, (Matrix.det (fun i j => C (group i) (f i) j)) ≠ 0 →
      saving ≤ (∑ i, degree (f i) : ℕ))
    (hsum : (∑ d : δ, s ^ degree d) ≤ Z) :
    ‖Matrix.det (fun i j => ∑ d, B i d * C (group i) d j)‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ saving * Z ^ Fintype.card ι := by
  classical
  let Q : ℝ := (Fintype.card ι).factorial * D ^ Fintype.card ι * ∏ i, L i
  have hQ : 0 ≤ Q := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))
    (Finset.prod_nonneg fun i _ => hL i)
  have hterm (f : ι → δ) :
      ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ ≤
        Q * s ^ saving * s ^ (∑ i, degree (f i)) := by
    by_cases hz : Matrix.det (fun i j => C (group i) (f i) j) = 0
    · rw [hz, mul_zero, norm_zero]
      positivity
    have hbp : (∏ i, ‖B i (f i)‖) ≤ ∏ i, L i * (s * s) ^ degree (f i) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hB i (f i))
    have hcp := FiniteDeterminantCollision.norm_det_le_factorial_mul_pow
      (fun i j => C (group i) (f i) j) hD (fun i j => hC _ _ _)
    have hpow : s ^ (∑ i, degree (f i)) ≤ s ^ saving := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_ge hs0 hs1.le (hsave f hz)
    rw [norm_mul, norm_prod]
    calc
      _ ≤ (∏ i, L i * (s * s) ^ degree (f i)) *
          ((Fintype.card ι).factorial * D ^ Fintype.card ι) :=
        mul_le_mul hbp hcp (norm_nonneg _) (Finset.prod_nonneg fun i _ =>
          mul_nonneg (hL i) (pow_nonneg (mul_self_nonneg s) _))
      _ = Q * ((s ^ (∑ i, degree (f i))) * s ^ (∑ i, degree (f i))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_pow]
        dsimp [Q]
        ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hQ) (pow_nonneg hs0.le (∑ i, degree (f i)))
  have hsum' : (∑ f : ι → δ, s ^ (∑ i, degree (f i))) =
      (∑ d : δ, s ^ degree d) ^ Fintype.card ι := by
    simp_rw [← Finset.prod_pow_eq_pow_sum]
    rw [← Fintype.prod_sum (fun (_ : ι) (d : δ) => s ^ degree d)]
    simp
  rw [FiniteDeterminantCollision.det_finite_row_sum group B C]
  calc
    _ ≤ ∑ f : ι → δ, ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ f : ι → δ, Q * s ^ saving * s ^ (∑ i, degree (f i)) :=
      Finset.sum_le_sum (fun f _ => hterm f)
    _ = Q * s ^ saving * (∑ d : δ, s ^ degree d) ^ Fintype.card ι := by
      rw [← Finset.mul_sum, hsum']
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg fun d _ => pow_nonneg hs0.le _) hsum _)
      (mul_nonneg hQ (Real.rpow_nonneg hs0.le _))

end Finite

section Infinite
variable {ι Γ μ : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise unconditional sums suffice; there is no unproved interchange of
an infinite sum with a determinant. -/
theorem infinite_degree_saving_bound
    (group : ι → Γ) (B : ι → μ → ℂ) (C : Γ → μ → ι → ℂ)
    (degree : μ → ℕ) (D s saving Z : ℝ) (L : ι → ℝ)
    (hD : 0 ≤ D) (hs0 : 0 < s) (hs1 : s < 1) (hZ : 0 ≤ Z) (hL : ∀ i, 0 ≤ L i)
    (hC : ∀ g d j, ‖C g d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ degree d)
    (hsave : ∀ f : ι → μ, (Matrix.det (fun i j => C (group i) (f i) j)) ≠ 0 →
      saving ≤ (∑ i, degree (f i) : ℕ))
    (hsum : ∀ S : Finset μ, (∑ d ∈ S, s ^ degree d) ≤ Z)
    (T : Matrix ι ι ℂ)
    (hseries : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (T i j)) :
    ‖T.det‖ ≤ ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
      s ^ saving * Z ^ Fintype.card ι := by
  classical
  let A : Finset μ → Matrix ι ι ℂ := fun S i j => ∑ d ∈ S, B i d * C (group i) d j
  have hlim : Tendsto A atTop (𝓝 T) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mpr (fun j => hseries i j)
  have hb (S : Finset μ) : ‖(A S).det‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ saving * Z ^ Fintype.card ι := by
    have h := finite_degree_saving_bound group (fun i (d : S) => B i d.val)
      (fun g (d : S) j => C g d.val j) (fun d : S => degree d.val)
      D s saving Z L hD hs0 hs1 hZ hL
      (fun g d j => hC g d.val j) (fun i d => hB i d.val)
      (fun f hf => hsave (fun i => (f i).val) hf) (by
        calc
          (∑ d : S, s ^ degree d.val) = ∑ d ∈ S, s ^ degree d :=
            Finset.sum_coe_sort S (fun d : μ => s ^ degree d)
          _ ≤ Z := hsum S)
    have he (i j : ι) : (∑ d : S, B i d.val * C (group i) d.val j) =
        ∑ d ∈ S, B i d * C (group i) d j :=
          Finset.sum_coe_sort S (fun d : μ => B i d * C (group i) d j)
    simpa only [he, A] using h
  exact le_of_tendsto' (((continuous_id.matrix_det.tendsto T).comp hlim).norm) hb

end Infinite

theorem multiIndex_geometric_sum_le {k : ℕ} (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (S : Finset (Fin k → ℕ)) : (∑ d ∈ S, s ^ (∑ r, d r)) ≤ ((1 - s)⁻¹) ^ k := by
  classical
  let N := S.sup (fun d => ∑ r, d r) + 1
  let box := Fintype.piFinset (fun _ : Fin k => Finset.range N)
  have hsub : S ⊆ box := by
    intro d hd
    apply Fintype.mem_piFinset.mpr
    intro r
    apply Finset.mem_range.mpr
    have hr : d r ≤ ∑ t, d t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    have hh := Finset.le_sup (f := fun d : Fin k → ℕ => ∑ t, d t) hd
    dsimp [N]
    omega
  have hsumN : (∑ n ∈ Finset.range N, s ^ n) ≤ (1 - s)⁻¹ := by
    simpa only [Fin.sum_univ_eq_sum_range] using Collision.sum_pow_fin_le_inv_one_sub hs0 hs1 N
  calc
    _ ≤ ∑ d ∈ box, s ^ (∑ r, d r) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hs0 _)
    _ = (∑ n ∈ Finset.range N, s ^ n) ^ k := by
      simp_rw [← Finset.prod_pow_eq_pow_sum]
      rw [show box = Fintype.piFinset (fun _ : Fin k => Finset.range N) from rfl,
        ← Finset.prod_univ_sum]
      simp
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => pow_nonneg hs0 n) hsumN k

/-- The capacity lemma supplies the degree saving for every nonzero grouped
coefficient determinant. The factor left for summation has exponent `k*M`. -/
theorem multivariate_capacity_bound {k : ℕ} {ι Γ : Type*}
    [Fintype ι] [DecidableEq ι]
    (group : ι → Γ) (B : ι → (Fin k → ℕ) → ℂ) (C : Γ → (Fin k → ℕ) → ι → ℂ)
    (low : Γ → Prop) [DecidablePred low] (capacity : Finset (Γ × (Fin k → ℕ)))
    (η S H D s : ℝ) (L : ι → ℝ)
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hD : 0 ≤ D) (hs0 : 0 < s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i) (hC : ∀ g d j, ‖C g d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ (∑ r, d r))
    (hcover : ∀ g d, low g → (∑ r, (d r : ℝ)) < S * H → (g, d) ∈ capacity)
    (hselected : η * Fintype.card ι ≤ ((Finset.univ.filter fun i => low (group i)).card : ℝ))
    (hcapacity : (capacity.card : ℝ) ≤ η * Fintype.card ι / 2)
    (T : Matrix ι ι ℂ)
    (hseries : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (T i j)) :
    ‖T.det‖ ≤ ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
      s ^ (η * Fintype.card ι * S * H / 2) * ((1 - s)⁻¹) ^ (k * Fintype.card ι) := by
  have hsave (f : ι → (Fin k → ℕ))
      (hf : Matrix.det (fun i j => C (group i) (f i) j) ≠ 0) :
      η * Fintype.card ι * S * H / 2 ≤ (∑ i, (∑ r, f i r) : ℕ) := by
    have hh := multivariate_collision_degree_sum_lower_bound
      (fun i => (group i, f i)) low (fun gd j => C gd.1 gd.2 j) (fun _ => 1)
      capacity η S H hS hH (by simpa using hf) hcover hselected hcapacity
    simpa only [Nat.cast_sum] using hh
  have hh := infinite_degree_saving_bound group B C (fun d => ∑ r, d r)
    D s (η * Fintype.card ι * S * H / 2) (((1 - s)⁻¹) ^ k) L hD hs0 hs1
    (by positivity) hL hC hB hsave (multiIndex_geometric_sum_le s hs0.le hs1) T hseries
  simpa only [pow_mul] using hh

end
end GeneralizedLogarithms.MultivariateInfiniteCollision

/-- info: 'GeneralizedLogarithms.MultivariateInfiniteCollision.infinite_degree_saving_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateInfiniteCollision.infinite_degree_saving_bound

/-- info: 'GeneralizedLogarithms.MultivariateInfiniteCollision.multivariate_capacity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateInfiniteCollision.multivariate_capacity_bound
