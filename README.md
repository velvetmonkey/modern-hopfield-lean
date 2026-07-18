# modern-hopfield-lean

[![thread](https://img.shields.io/badge/%F0%9F%A7%B5-how%20it%20works-1DA1F2)](https://x.com/thevelvetmonke)
[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](ModernHopfield)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20480641.svg)](https://doi.org/10.5281/zenodo.20480641)

**modern-hopfield-lean: Formal Proofs for Continuous Modern Hopfield Networks in Lean 4**

Lean 4 formal proofs for a continuous modern Hopfield network in the style of
Ramsauer et al. (2020). The development covers the log-sum-exp energy, softmax
update map, energy descent under the update rule, boundedness below of the
energy, convergence of the energy sequence, and a fixed-point characterisation.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`).

## What this is, and why it matters

This library formalizes the energy argument for a finite-dimensional continuous modern Hopfield network. Its headline theorem, `ModernHopfield.energy_sequence_converges`, proves that the energy values along repeated softmax updates converge to some real limit.

The proof has two machine-checked parts. Convexity of log-sum-exp and an exact tangent inequality show that one update cannot increase the energy. A separate estimate provides a uniform lower bound. Standard monotone convergence for real sequences then yields the limiting energy value.

The conclusion concerns energy only. It does not prove that the state vectors converge, that the limit is a fixed point, that a stored pattern is retrieved, or that the network has a particular memory capacity. The model also uses exact finite real arithmetic and does not cover trained or approximate implementations.

## Setting

The network stores `M` patterns in `Fin N -> ℝ`, represented as
`ξ : Fin M -> Fin N -> ℝ`, with positive inverse temperature `β`. For a state
`x : Fin N -> ℝ`, the score vector is `mulVec ξ x`, the softmax weights are
`softmax β (mulVec ξ x)`, and the update is the weighted pattern combination

```lean
Setup.update s x = vecMul (softmax s.β (mulVec s.ξ x)) s.ξ
```

The energy is

```lean
Setup.energy s x = -lse s.β (mulVec s.ξ x) + (1 / 2) * sqNorm x + s.C
```

where `lse` is the log-sum-exp potential. The main result is that this energy
is non-increasing along the update sequence, is bounded below, and therefore
the energy sequence converges. The library also records the fixed-point equation
for the update map.

## Theorem Inventory

| Module | Name | Statement |
| --- | --- | --- |
| `ModernHopfield.Defs` | `exp_sum_pos` | `0 < ∑ i : Fin M, Real.exp (β * v i)` |
| `ModernHopfield.Defs` | `softmax_nonneg` | `0 ≤ softmax β v i` |
| `ModernHopfield.Defs` | `softmax_sum` | `∑ i : Fin M, softmax β v i = 1` |
| `ModernHopfield.Defs` | `sum_mul_mulVec_eq_dot_vecMul` | `∑ μ : Fin M, p μ * mulVec ξ y μ = dot (vecMul p ξ) y` |
| `ModernHopfield.Defs` | `dot_comm` | `dot a b = dot b a` |
| `ModernHopfield.Defs` | `sqNorm_eq_dot` | `sqNorm x = dot x x` |
| `ModernHopfield.Defs` | `sqNorm_nonneg` | `0 ≤ sqNorm x` |
| `ModernHopfield.Defs` | `sqNorm_sub_eq` | `sqNorm (a - b) = sqNorm a - 2 * dot a b + sqNorm b` |
| `ModernHopfield.Defs` | `dot_le_half_sqNorm_add` | `dot a b ≤ (1 / 2) * (sqNorm a + sqNorm b)` |
| `ModernHopfield.Defs` | `mulVec_le_half_add` | `mulVec ξ x μ ≤ (1 / 2) * sqNorm (ξ μ) + (1 / 2) * sqNorm x` |
| `ModernHopfield.EnergyDescent` | `exp_sum_le` | `Real.exp (∑ i : Fin M, w i * x i) ≤ ∑ i : Fin M, w i * Real.exp (x i)` under nonnegative weights summing to `1` |
| `ModernHopfield.EnergyDescent` | `lse_tangent` | `lse β v + ∑ i : Fin M, softmax β v i * (v' i - v i) ≤ lse β v'` |
| `ModernHopfield.EnergyDescent` | `lse_convex` | `ConvexOn ℝ Set.univ (fun v : Fin M -> ℝ => lse β v)` |
| `ModernHopfield.EnergyDescent` | `energy_descent` | `s.energy (s.update x) ≤ s.energy x` |
| `ModernHopfield.EnergyDescent` | `energy_bounded_below` | `∃ B : ℝ, ∀ x : Fin N -> ℝ, B ≤ s.energy x` |
| `ModernHopfield.Convergence` | `energy_sequence_converges` | `∃ L : ℝ, Filter.Tendsto (fun k => s.energy (s.iterate x₀ k)) Filter.atTop (nhds L)` |
| `ModernHopfield.Convergence` | `fixed_point_characterisation` | `s.update x = x ↔ x = vecMul (softmax s.β (mulVec s.ξ x)) s.ξ` |

## Modules

- `ModernHopfield.Defs`: log-sum-exp, softmax, vector operations, setup, energy, update, and algebraic helper lemmas.
- `ModernHopfield.EnergyDescent`: Jensen inequality for `exp`, log-sum-exp tangent inequality, convexity, energy descent, and lower boundedness.
- `ModernHopfield.Convergence`: convergence of the energy sequence and fixed-point characterisation.

## Build

```bash
lake build
rg "sorry|admit" ModernHopfield/
```

The library targets Lean 4.28.0 and Mathlib v4.28.0.

## Author

Ben Cassie
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
