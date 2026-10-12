import GeneralizedLogarithms.MultivariateDecayParameters

/-! Simultaneous choice of the auxiliary dimension and all numerical slacks. -/

namespace GeneralizedLogarithms.MultivariateFixedParameters

noncomputable section
open scoped BigOperators Topology
open Filter LogIrrationalityMeasure.LogExponent MultivariateParameters
open MultivariateDecayParameters

variable {k : ℕ} {ν : ℝ}

def gap (P : Parameters k ν) : ℝ := (ν+1)*(P.A : ℝ)*(1-P.η)-1-ν*P.θ
def count (P : Parameters k ν) (m : ℕ) : ℕ := ⌊(P.C : ℝ)^m⌋₊
def w₀ (P : Parameters k ν) (m : ℕ) : ℚ := (1/P.B)^m
def v₀ (P : Parameters k ν) (m : ℕ) : ℚ := (P.D/P.B)^m
def epsilon (P : Parameters k ν) (m : ℕ) : ℝ := (P.σ : ℝ)/((k+m : ℕ)+1)
def radius (K : ℕ) (L : ℝ) : ℝ := 100*K*(1+L)
def weightNumerator (k K : ℕ) (ν R : ℝ) : ℝ :=
  Real.log (2*k*R)+Real.log 4+(Real.log K+ν)+Real.log (max 1 (k : ℝ))

theorem count_pos (P : Parameters k ν) (m : ℕ) : 0 < count P m := by
  apply Nat.floor_pos.mpr
  exact one_le_pow₀ P.one_lt_C.le

theorem w₀_pos (P : Parameters k ν) (m : ℕ) : 0 < w₀ P m := by
  exact pow_pos (div_pos zero_lt_one (by exact_mod_cast P.B_pos)) _

theorem v₀_pos (P : Parameters k ν) (m : ℕ) : 0 < v₀ P m := by
  exact pow_pos (div_pos (by exact_mod_cast P.B_pos.trans P.B_lt_D) (by exact_mod_cast P.B_pos)) _

theorem ratio_eq (P : Parameters k ν) (m : ℕ) :
    ((w₀ P m : ℚ) : ℝ)/(v₀ P m : ℝ) = (1/(P.D : ℝ))^m := by
  simp only [w₀,v₀,Rat.cast_pow,Rat.cast_div,Rat.cast_one,← div_pow]
  field_simp [P.B_pos.ne']

structure Fixed (P : Parameters k ν) (Lden Lomega : ℝ) where
  m : ℕ
  m_pos : 0 < m
  F : ℝ
  S : ℝ
  W : ℝ
  F_pos : 0 < F
  F_theta : 1/(P.θ : ℝ) ≤ F
  S_pos : 0 < S
  W_one : 1 ≤ W
  low_gap : 1+ν*P.θ+Real.log (3/4)*P.η*S/2 ≤ -gap P
  volume : (count P m : ℝ)*(1+3*(P.σ : ℝ))^(k+m)*((w₀ P m : ℝ)/v₀ P m)^k*(P.θ : ℝ)^m < 1
  longitudinal : ∀ r d : ℕ, r<k → 1≤d-r → d-r≤k → d≤2*k-1 →
    (d : ℝ)^d/(epsilon P m)^d < (P.θ : ℝ)^r*((w₀ P m : ℝ)/v₀ P m)^(d-r)
  capacity : ((k+m).choose k : ℝ)*(v₀ P m : ℝ)^k*(P.A : ℝ)^m*S^k /
    ((count P m : ℝ)*(P.θ : ℝ)^m) < P.η/2
  analytic_cost : (ν+1)/F+radius (count P m) Lomega/(w₀ P m : ℝ)+2*Real.log 2/(v₀ P m : ℝ)+
    weightNumerator k (count P m) ν (radius (count P m) Lomega)/W < gap P/2
  arithmetic_cost : (count P m : ℝ)*Lden/(w₀ P m : ℝ)+
    Arithmetic.lcmConstant*F*m/(v₀ P m : ℝ)+Arithmetic.lcmConstant*m/W < gap P/2

theorem exists_fixed (hk : 1 ≤ k) (hν : 0 ≤ ν) (P : Parameters k ν)
    (Lden Lomega : ℝ) : Nonempty (Fixed P Lden Lomega) := by
  let g := gap P
  have hg : 0 < g := P.arithmetic_gap
  let e := g/8
  have he : 0 < e := div_pos hg (by norm_num)
  obtain ⟨F,hF⟩ := exists_gt (max 1 (max (1/(P.θ : ℝ)) ((ν+1)/e)))
  have hF1 : 1 < F := (le_max_left _ _).trans_lt hF
  have hF0 : 0 < F := zero_lt_one.trans hF1
  have hFt : 1/(P.θ : ℝ) ≤ F := ((le_max_left _ _).trans (le_max_right _ _)).trans hF.le
  have hFe : (ν+1)/F < e := by
    have hh : (ν+1)/e < F := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hF
    exact (div_lt_iff₀ hF0).mpr (by nlinarith [(div_lt_iff₀ he).mp hh])
  have hlog : Real.log (3/4 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  let S := 2*(1+ν*(P.θ : ℝ)+g+1)/(-Real.log (3/4)*P.η)
  have hS : 0 < S := div_pos
    (by have := mul_nonneg hν P.theta_pos.le; positivity)
    (mul_pos (neg_pos.mpr hlog) P.eta_pos)
  have hSgap : 1+ν*(P.θ : ℝ)+Real.log (3/4)*P.η*S/2 ≤ -g := by
    have hn : Real.log (3/4 : ℝ) ≠ 0 := hlog.ne
    have heq : Real.log (3/4)*P.η*S/2 = -(1+ν*(P.θ : ℝ)+g+1) := by
      dsimp [S]
      field_simp [P.eta_pos.ne']
      <;> ring
    rw [heq]
    linarith
  have hC0 := zero_lt_one.trans P.one_lt_C
  have hD0 := P.B_pos.trans P.B_lt_D
  have hAm := P.theta_pos.trans P.theta_lt_A
  have hσ := P.sigma_pos
  have hv := LongitudinalAsymptotics.eventually_volume_inequality k P.C P.θ P.D (1+3*(P.σ : ℝ))
    hC0.le P.theta_pos.le hD0 (by positivity)
    (by convert P.volume_margin using 1 <;> ring)
  have hl := LongitudinalAsymptotics.eventually_longitudinal_gap k hk P.θ P.D P.σ
    P.theta_pos (P.theta_lt_A.trans P.A_lt_one).le hD0 P.D_lt_one P.sigma_pos
  have hcap := tendsto_capacity_ratio k P.B P.C P.D P.θ P.A S
    P.B_pos P.one_lt_C hD0 P.theta_pos hAm P.D_pow_lt_collision_scale
  have han := (tendsto_center_cost P.B P.C (100*(1+Lomega)) P.B_pos hC0.le P.CB_lt_one).add
    (tendsto_longitudinal_cost P.B P.D (2*Real.log 2) P.B_pos P.B_lt_D)
  have har := (tendsto_center_cost P.B P.C Lden P.B_pos hC0.le P.CB_lt_one).add
    (tendsto_cutoff_cost P.B P.D (Arithmetic.lcmConstant*F) P.B_pos P.B_lt_D)
  simp only [zero_add] at han har
  have hex := hv.and (hl.and ((hcap.eventually (gt_mem_nhds (half_pos P.eta_pos))).and
    ((han.eventually (gt_mem_nhds he)).and ((har.eventually (gt_mem_nhds he)).and (eventually_ge_atTop (1 : ℕ))))))
  obtain ⟨m, hvm, hlm, hcm, ham, harm, hm⟩ := hex.exists
  let E := weightNumerator k (count P m) ν (radius (count P m) Lomega)
  obtain ⟨W,hW⟩ := exists_gt (max 1 (max (E/e) (Arithmetic.lcmConstant*m/e)))
  have hW1 : 1 < W := (le_max_left _ _).trans_lt hW
  have hW0 := zero_lt_one.trans hW1
  have hEW : E/W < e := by
    have hh : E/e < W := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hW
    exact (div_lt_iff₀ hW0).mpr (by nlinarith [(div_lt_iff₀ he).mp hh])
  have hLW : Arithmetic.lcmConstant*m/W < e := by
    have hh : Arithmetic.lcmConstant*m/e < W := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hW
    exact (div_lt_iff₀ hW0).mpr (by nlinarith [(div_lt_iff₀ he).mp hh])
  refine ⟨⟨m,by omega,F,S,W,hF0,hFt,hS,hW1.le,hSgap,?_,?_,?_,?_,?_⟩⟩
  · simpa only [count,ratio_eq] using hvm
  · simpa only [ratio_eq,epsilon,Nat.cast_add,Nat.cast_one] using hlm
  · simpa only [v₀,count,Rat.cast_pow,Rat.cast_div] using hcm
  · have han' : radius (count P m) Lomega/(w₀ P m : ℝ)+2*Real.log 2/(v₀ P m : ℝ) < e := by
      convert ham using 1 <;> simp only [radius,count,w₀,v₀,Rat.cast_pow,Rat.cast_div,Rat.cast_one] <;> ring
    change (ν+1)/F+radius (count P m) Lomega/(w₀ P m : ℝ)+2*Real.log 2/(v₀ P m : ℝ)+E/W < g/2
    dsimp [e] at *
    linarith
  · have har' : (count P m : ℝ)*Lden/(w₀ P m : ℝ)+
        Arithmetic.lcmConstant*F*m/(v₀ P m : ℝ) < e := by
      simpa only [count,w₀,v₀,Rat.cast_pow,Rat.cast_div,Rat.cast_one] using harm
    change _ < g/2
    dsimp [e] at *
    linarith

end
end GeneralizedLogarithms.MultivariateFixedParameters

/-- info: 'GeneralizedLogarithms.MultivariateFixedParameters.exists_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeneralizedLogarithms.MultivariateFixedParameters.exists_fixed
