/-
Copyright (c) 2025. All rights reserved.
Energy descent and convexity for the modern Hopfield network.
-/
import ModernHopfield.Defs

noncomputable section

open Finset Real BigOperators

namespace ModernHopfield

variable {M N : ℕ} [NeZero M]

/-! ## Jensen's inequality for exp (finite weighted version) -/

/-
Finite Jensen's inequality for `exp`: if weights are non-negative and sum to 1,
    then `exp(Σ wᵢ xᵢ) ≤ Σ wᵢ exp(xᵢ)`.
-/
omit [NeZero M] in
lemma exp_sum_le (w x : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1) :
    Real.exp (∑ i : Fin M, w i * x i) ≤ ∑ i : Fin M, w i * Real.exp (x i) := by
  -- The exponential function is convex, so we can apply Jensen's inequality.
  have h_convex : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
    exact convexOn_exp;
  convert h_convex.map_sum_le _ _ _ <;> aesop

/-! ## Tangent inequality for log-sum-exp -/

/-
The tangent (first-order convexity) inequality for log-sum-exp:
    `lse(β, v) + ⟨softmax(β,v), v' - v⟩ ≤ lse(β, v')`.
-/
theorem lse_tangent (β : ℝ) (hβ : 0 < β) (v v' : Fin M → ℝ) :
    lse β v + ∑ i : Fin M, softmax β v i * (v' i - v i) ≤ lse β v' := by
  -- By exp_sum_le (Jensen for exp) with weights w and values β*(v'_i - v_i):
  have h_exp_sum_le : Real.exp (∑ i, (softmax β v i) * β * (v' i - v i)) ≤ ∑ i, (softmax β v i) * Real.exp (β * (v' i - v i)) := by
    convert exp_sum_le _ _ ( fun i => softmax_nonneg β v i ) ( softmax_sum β v ) using 1;
    simp +decide only [mul_assoc];
  -- The RHS: S * w_i * exp(β (�*(v�'_i - v_i)) = S*w_i * exp (�(�β*(v'_i - v_i)) = exp(β*v_i) * exp( �β�*(v'_i - v_i)) = exp(β*v'_i)
  have h_rhs : ∑ i, (softmax β v i) * Real.exp (β * (v' i - v i)) = (∑ i, Real.exp (β * v' i)) / (∑ i, Real.exp (β * v i)) := by
    simp +decide only [softmax];
    rw [ Finset.sum_div _ _ _ ] ; congr ; ext i ; rw [ div_mul_eq_mul_div, ← Real.exp_add ] ; ring_nf;
  unfold lse;
  rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_add', div_le_div_iff_of_pos_right ] <;> try positivity;
  have := Real.log_le_log ( by positivity ) h_exp_sum_le;
  rw [ h_rhs, Real.log_div ( by exact ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty ) ( by exact ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty ) ] at this ; norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] at * ; linarith

/-! ## Convexity of log-sum-exp -/

/-
Log-sum-exp is convex.
-/
set_option linter.unusedSimpArgs false in
theorem lse_convex (β : ℝ) (hβ : 0 < β) :
    ConvexOn ℝ Set.univ (fun v : Fin M → ℝ => lse β v) := by
  refine' ⟨ convex_univ, fun v _ w _ a b ha hb hab => _ ⟩;
  have h1 := lse_tangent _ hβ ( a • v + b • w ) v; have h2 := lse_tangent _ hβ ( a • v + b • w ) w; simp_all +decide [ mul_sub, sub_sub_eq_add_sub, mul_add, add_assoc ] ;
  simp_all +decide [ Finset.sum_add_distrib, mul_add, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, ← eq_sub_iff_add_eq' ];
  nlinarith

/-! ## Energy descent -/

/-
**Energy descent**: `E(x_{k+1}) ≤ E(x_k)` — the energy is non-increasing
    under the Hopfield update rule.
-/
theorem energy_descent (s : Setup M N) (x : Fin N → ℝ) :
    s.energy (s.update x) ≤ s.energy x := by
  unfold ModernHopfield.Setup.energy ModernHopfield.Setup.update;
  have := lse_tangent s.β s.hβ ( mulVec s.ξ x ) ( mulVec s.ξ ( vecMul ( softmax s.β ( mulVec s.ξ x ) ) s.ξ ) );
  simp_all +decide [ mul_sub, Finset.sum_sub_distrib ];
  rw [ sum_mul_mulVec_eq_dot_vecMul, sum_mul_mulVec_eq_dot_vecMul ] at this;
  have := sqNorm_sub_eq ( vecMul ( softmax s.β ( mulVec s.ξ x ) ) s.ξ ) x;
  linarith [ sqNorm_nonneg ( vecMul ( softmax s.β ( mulVec s.ξ x ) ) s.ξ - x ), sqNorm_eq_dot ( vecMul ( softmax s.β ( mulVec s.ξ x ) ) s.ξ ) ]

/-! ## Energy lower bound -/

/-
**Energy is bounded below**: there exists a uniform lower bound on the energy.
-/
theorem energy_bounded_below (s : Setup M N) :
    ∃ B : ℝ, ∀ x : Fin N → ℝ, B ≤ s.energy x := by
  -- We first make a bound for the log-sum-exp part:
  have h_lse_bound : ∀ x : Fin N → ℝ, lse s.β (mulVec s.ξ x) ≤ (1 / 2) * sqNorm x + (1 / s.β) * Real.log (∑ μ : Fin M, Real.exp ((s.β / 2) * sqNorm (s.ξ μ))) := by
    intro x;
    -- Apply the inequality `mulVec_le_half_add` to each term in the sum.
    have h_sum_bound : ∑ μ : Fin M, Real.exp (s.β * mulVec s.ξ x μ) ≤ Real.exp ((s.β / 2) * sqNorm x) * ∑ μ : Fin M, Real.exp ((s.β / 2) * sqNorm (s.ξ μ)) := by
      rw [ Finset.mul_sum _ _ _ ];
      gcongr;
      rw [ ← Real.exp_add ] ; exact Real.exp_le_exp.mpr ( by have := mulVec_le_half_add s.ξ x ‹_›; norm_num at *; nlinarith [ s.hβ ] );
    unfold lse; rw [ one_div, inv_mul_le_iff₀ ( s.hβ ) ] ;
    convert Real.log_le_log ( exp_sum_pos s.β _ ) h_sum_bound using 1 ; rw [ Real.log_mul ( by positivity ) ( by exact ne_of_gt ( Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty ) ), Real.log_exp ] ; ring_nf ; norm_num [ s.hβ.ne' ];
  exact ⟨ s.C - ( 1 / s.β ) * Real.log ( ∑ μ, Real.exp ( s.β / 2 * sqNorm ( s.ξ μ ) ) ), fun x => by unfold ModernHopfield.Setup.energy; linarith [ h_lse_bound x ] ⟩

end ModernHopfield
