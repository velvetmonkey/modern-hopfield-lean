/-
Copyright (c) 2025. All rights reserved.
Convergence of the modern Hopfield network energy sequence and fixed-point characterisation.
-/
import ModernHopfield.EnergyDescent

noncomputable section

open Finset Real BigOperators Filter

namespace ModernHopfield

variable {M N : ℕ} [NeZero M]

/-
The energy sequence `E(x_k)` converges: bounded monotone sequences converge.
-/
theorem energy_sequence_converges (s : Setup M N) (x₀ : Fin N → ℝ) :
    ∃ L : ℝ, Filter.Tendsto (fun k => s.energy (s.iterate x₀ k)) Filter.atTop (nhds L) := by
  constructor;
  convert tendsto_atTop_ciInf ( show Antitone fun k => s.energy ( s.iterate x₀ k ) from fun n m hnm => ?_ ) ?_;
  · induction' hnm with k hk ih <;> [ tauto; exact le_trans ( energy_descent s _ ) ih ];
  · exact ⟨ _, Set.forall_mem_range.mpr fun k => energy_bounded_below s |> Classical.choose_spec |> fun h => h _ ⟩

/-
**Fixed-point characterisation**: `x` is a fixed point of the update rule if and only if
    `x = ξ · softmax(β · ξᵀ · x)`.
-/
theorem fixed_point_characterisation (s : Setup M N) (x : Fin N → ℝ) :
    s.update x = x ↔ x = vecMul (softmax s.β (mulVec s.ξ x)) s.ξ := by
  exact eq_comm

end ModernHopfield