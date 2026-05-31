/-
Copyright (c) 2025. All rights reserved.
Modern Hopfield Network formalization (Ramsauer et al. 2020).
-/
import Mathlib

noncomputable section

open Finset Real BigOperators

namespace ModernHopfield

variable {M N : ℕ}

/-! ## Core definitions -/

/-- Log-sum-exp: `lse β v = (1/β) · log(Σᵢ exp(β · vᵢ))` -/
def lse (β : ℝ) (v : Fin M → ℝ) : ℝ :=
  (1 / β) * Real.log (∑ i : Fin M, Real.exp (β * v i))

/-- Softmax: `softmax(β, v)ᵢ = exp(β · vᵢ) / Σⱼ exp(β · vⱼ)` -/
def softmax (β : ℝ) (v : Fin M → ℝ) (i : Fin M) : ℝ :=
  Real.exp (β * v i) / ∑ j : Fin M, Real.exp (β * v j)

/-- Dot product of two vectors. -/
def dot (a b : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, a j * b j

/-- Matrix-vector product: `(mulVec ξ x)ᵢ = Σⱼ ξᵢⱼ · xⱼ` (represents ξᵀx). -/
def mulVec (ξ : Fin M → Fin N → ℝ) (x : Fin N → ℝ) (i : Fin M) : ℝ :=
  ∑ j : Fin N, ξ i j * x j

/-- Vector-matrix product: `(vecMul p ξ)ⱼ = Σᵢ pᵢ · ξᵢⱼ` (weighted combination of patterns). -/
def vecMul (p : Fin M → ℝ) (ξ : Fin M → Fin N → ℝ) (j : Fin N) : ℝ :=
  ∑ i : Fin M, p i * ξ i j

/-- Squared Euclidean norm: `sqNorm x = Σⱼ xⱼ²`. -/
def sqNorm (x : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, x j ^ 2

/-- The modern Hopfield network setup, bundling stored patterns, inverse temperature,
    and an energy constant. -/
structure Setup (M N : ℕ) [NeZero M] where
  /-- Stored patterns: M patterns in ℝᴺ -/
  ξ : Fin M → Fin N → ℝ
  /-- Inverse temperature -/
  β : ℝ
  /-- Inverse temperature is positive -/
  hβ : 0 < β
  /-- Additive constant in energy -/
  C : ℝ

variable [NeZero M]

/-- Energy function: `E(x) = -lse(β, ξᵀx) + ½‖x‖² + C` -/
def Setup.energy (s : Setup M N) (x : Fin N → ℝ) : ℝ :=
  -lse s.β (mulVec s.ξ x) + (1 / 2) * sqNorm x + s.C

/-- Update rule: `x ↦ ξ · softmax(β · ξᵀ · x)` -/
def Setup.update (s : Setup M N) (x : Fin N → ℝ) : Fin N → ℝ :=
  vecMul (softmax s.β (mulVec s.ξ x)) s.ξ

/-- Iterated update: `x_k` starting from `x₀`. -/
def Setup.iterate (s : Setup M N) (x₀ : Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => x₀
  | k + 1 => s.update (s.iterate x₀ k)

/-! ## Basic properties -/

/-
The sum of exponentials is positive (since M ≥ 1).
-/
lemma exp_sum_pos (β : ℝ) (v : Fin M → ℝ) : 0 < ∑ i : Fin M, Real.exp (β * v i) := by
  exact Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty

/-
Softmax outputs are non-negative.
-/
omit [NeZero M] in
lemma softmax_nonneg (β : ℝ) (v : Fin M → ℝ) (i : Fin M) : 0 ≤ softmax β v i := by
  exact div_nonneg ( Real.exp_nonneg _ ) ( Finset.sum_nonneg fun _ _ => Real.exp_nonneg _ )

/-
Softmax outputs sum to 1.
-/
lemma softmax_sum (β : ℝ) (v : Fin M → ℝ) : ∑ i : Fin M, softmax β v i = 1 := by
  unfold softmax;
  rw [ ← Finset.sum_div, div_self <| ne_of_gt <| Finset.sum_pos ( fun _ _ => Real.exp_pos _ ) Finset.univ_nonempty ]

/-
Rewriting identity: Σ_μ p_μ (ξᵀy)_μ = dot(ξ·p, y).
-/
omit [NeZero M] in
lemma sum_mul_mulVec_eq_dot_vecMul (p : Fin M → ℝ) (ξ : Fin M → Fin N → ℝ) (y : Fin N → ℝ) :
    ∑ μ : Fin M, p μ * mulVec ξ y μ = dot (vecMul p ξ) y := by
  simp +decide only [mulVec, dot, vecMul];
  simpa only [ mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul ] using Finset.sum_comm

/-
dot(a,b) = dot(b,a).
-/
lemma dot_comm (a b : Fin N → ℝ) : dot a b = dot b a := by
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-
sqNorm x = dot x x.
-/
lemma sqNorm_eq_dot (x : Fin N → ℝ) : sqNorm x = dot x x := by
  exact Finset.sum_congr rfl fun _ _ => sq _

/-
sqNorm is non-negative.
-/
lemma sqNorm_nonneg (x : Fin N → ℝ) : 0 ≤ sqNorm x := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-
Expansion of sqNorm(a - b).
-/
lemma sqNorm_sub_eq (a b : Fin N → ℝ) :
    sqNorm (a - b) = sqNorm a - 2 * dot a b + sqNorm b := by
  unfold sqNorm dot
  simp +decide [sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, mul_assoc, mul_comm,
    mul_left_comm]

/-
AM-GM bound on dot product: dot(a,b) ≤ ½(sqNorm a + sqNorm b).
-/
lemma dot_le_half_sqNorm_add (a b : Fin N → ℝ) :
    dot a b ≤ (1 / 2) * (sqNorm a + sqNorm b) := by
  unfold dot sqNorm;
  rw [ ← Finset.sum_add_distrib, Finset.mul_sum ] ; exact Finset.sum_le_sum fun i _ => by linarith [ sq_nonneg ( a i - b i ) ] ;

/-
AM-GM bound on mulVec: (ξᵀx)_μ ≤ ½ sqNorm(ξ_μ) + ½ sqNorm(x).
-/
omit [NeZero M] in
lemma mulVec_le_half_add (ξ : Fin M → Fin N → ℝ) (x : Fin N → ℝ) (μ : Fin M) :
    mulVec ξ x μ ≤ (1 / 2) * sqNorm (ξ μ) + (1 / 2) * sqNorm x := by
  convert dot_le_half_sqNorm_add ( ξ μ ) x using 1;
  ring

end ModernHopfield