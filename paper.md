# modern-hopfield-lean: Formal Proofs for Continuous Modern Hopfield Networks in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
2026-05-31

## Abstract

`modern-hopfield-lean` is a Lean 4 / Mathlib library formalising energy descent for a continuous modern Hopfield network in the style of Ramsauer et al. (2020). The development defines log-sum-exp, softmax, finite vector operations, the network setup, the energy, the update rule, log-sum-exp convexity facts, energy descent, a lower energy bound, convergence of the energy sequence, and a fixed-point characterisation. The proof method combines a log-sum-exp tangent inequality with a quadratic energy identity. The library is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

Modern Hopfield networks reinterpret associative memory through continuous states and attention-like softmax updates. In the formulation of Ramsauer et al., stored patterns interact with a state through log-sum-exp energy. The update map computes softmax weights over pattern scores and returns the weighted combination of patterns.

The central stability fact is energy descent: applying the update does not increase the energy. This makes the network a natural member of the Lyapunov and energy-descent family of formal developments. The Lean repository proves this descent result and the consequent convergence of the scalar energy sequence.

## 2. Mathematical Setting

The network stores `M` patterns in `Fin N -> Real`, represented by

```text
xi : Fin M -> Fin N -> Real.
```

For a state `x`, `mulVec xi x` computes the vector of pattern scores. The log-sum-exp potential is

```text
lse beta v = (1 / beta) * log(sum_i exp(beta * v_i)).
```

The softmax weights are

```text
softmax beta v i =
  exp(beta * v_i) / sum_j exp(beta * v_j).
```

The update is the weighted pattern combination

```text
update x = vecMul (softmax beta (mulVec xi x)) xi.
```

The energy is

```text
E(x) = -lse beta (mulVec xi x) + 1/2 * ||x||^2 + C.
```

## 3. Main Theorems

`Defs.lean` proves basic facts: `exp_sum_pos`, `softmax_nonneg`, `softmax_sum`, dot-product and squared-norm identities, `dot_le_half_sqNorm_add`, and `mulVec_le_half_add`.

`EnergyDescent.lean` proves the finite Jensen inequality `exp_sum_le`, the log-sum-exp tangent inequality

```text
lse beta v + sum_i softmax beta v i * (v'_i - v_i)
  <= lse beta v',
```

and `lse_convex`. The main descent theorem is

```text
energy_descent:
  s.energy (s.update x) <= s.energy x.
```

The theorem `energy_bounded_below` proves that there is a uniform lower bound for the energy.

`Convergence.lean` proves

```text
energy_sequence_converges:
  exists L, Tendsto (fun k => s.energy (s.iterate x0 k)) atTop (nhds L),
```

and

```text
fixed_point_characterisation:
  s.update x = x <-> x = vecMul (softmax s.beta (mulVec s.xi x)) s.xi.
```

## 4. Proof Sketch

The descent proof uses the tangent inequality for log-sum-exp at the current score vector. The update is chosen so that the tangent term can be rewritten using the dot-product identity between `mulVec` and `vecMul`. Expanding the squared norm difference gives a negative squared-distance contribution, which yields `E(update x) <= E(x)`.

The lower-bound proof controls the log-sum-exp term using the AM-GM style inequality `dot a b <= 1/2(||a||^2 + ||b||^2)`. Energy convergence follows because the scalar energy sequence is monotone nonincreasing by `energy_descent` and bounded below by `energy_bounded_below`.

## 5. Relation to Sibling Libraries

`modern-hopfield-lean` extends the energy-descent theme of `hopfield-lean`, DOI `10.5281/zenodo.20474169`, from finite-state Hopfield networks to continuous softmax updates. It also relates to `mirror-descent-lean`, DOI `10.5281/zenodo.20475033`, through log-sum-exp and convexity, and to `lyapunov-odes-lean`, DOI `10.5281/zenodo.20475912`, through the general idea of proving convergence from an energy function.

## 6. Conclusion

`modern-hopfield-lean` provides a Lean 4 proof of the core energy descent and fixed-point algebra for continuous modern Hopfield networks. It formalises log-sum-exp, softmax, the update, energy descent, lower boundedness, and scalar energy convergence. Future work could connect the energy convergence theorem to convergence of states, basin analysis, and attention mechanisms used in transformer architectures.

## References

Ramsauer, H., Schaefl, B., Lehner, J., Seidl, P., Widrich, M., Adler, T., Gruber, L., Holzleitner, M., Pavlovic, M., Sandve, G. K., Greiff, V., Kreil, D., Kopp, M., Klambauer, G., Brandstetter, J., and Hochreiter, S. (2020). *Hopfield Networks is All You Need*. arXiv:2008.02217.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *hopfield-lean: Lean 4 Formal Proofs of Hopfield Network Energy Descent and Attractor Convergence*. Zenodo. <https://doi.org/10.5281/zenodo.20474169>

Cassie, B. (2026). *mirror-descent-lean: Formal Proofs of Mirror Descent and Bregman Divergence Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20475033>

Cassie, B. (2026). *lyapunov-odes-lean*. Zenodo. <https://doi.org/10.5281/zenodo.20475912>
