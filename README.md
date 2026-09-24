# Shapley value axiomatic characterization in Lean 4

A Lean 4 + Mathlib formalization of the **Shapley value** and its axiomatic
characterization (Shapley, 1953): the Shapley value is the *unique* value
satisfying efficiency, symmetry, the null-player property, and additivity.

## Mathematics

Finite player type `N` with `[Fintype N]`, `n = Fintype.card N`. A game is
`v : Finset N → ℝ` with `v ∅ = 0`. The Shapley value of player `i` in game `v`:

```
φᵢ(v) = ∑_{S : Finset N, i ∈ S} ((|S|-1)! (n-|S|)! / n!) * (v S - v (S \ {i}))
```

A *value* `ψ` maps games to payoff vectors `N → ℝ`. The four axioms:

1. **Efficiency**: `∑ i, ψ v i = v Finset.univ`
2. **Symmetry**: symmetric players in `v` get equal payoffs
3. **Null player**: a player contributing nothing gets `0`
4. **Additivity**: `ψ (v + w) = ψ v + ψ w` pointwise

Main results (see `ShapleyValue/Basic.lean`, `ShapleyValue/Existence.lean`,
and `ShapleyValue/Uniqueness.lean`):

- `ShapleyValue.shapleyValue_efficient`, `..._symmetric`,
  `..._nullPlayer`, `..._additive`: the Shapley value satisfies the axioms.
- `ShapleyValue.shapleyValue_unique`: any value satisfying the four axioms
  equals `shapleyValue` (via unanimity games and the Möbius decomposition).
- `ShapleyValue.shapley_characterization`: the iff combining both directions.

The development is sorry-free and axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`).

## Results

The Palomar proof surface contains six checked theorems:

- `ShapleyValue.Palomar.shapley_characterization`
- `ShapleyValue.Palomar.shapleyValue_unique`
- `ShapleyValue.Palomar.shapleyValue_efficient`
- `ShapleyValue.Palomar.shapleyValue_symmetric`
- `ShapleyValue.Palomar.shapleyValue_nullPlayer`
- `ShapleyValue.Palomar.shapleyValue_additive`

The library is organized as follows:

- `ShapleyValue/Basic.lean` defines finite cooperative games, the Shapley weight
  and formula, and the four axioms.
- `ShapleyValue/Existence.lean` proves efficiency, symmetry, the null-player
  property, and additivity for the Shapley formula.
- `ShapleyValue/Uniqueness.lean` develops unanimity games and Möbius inversion
  and proves uniqueness and the characterization.
- `Challenge.lean` and `Solution.lean` provide the standalone Palomar statement
  and proof surface.
- `scripts/verify-palomar.sh` checks the package shape, import closure,
  compilation, and axiom report.

## Palomar

This repository is packaged for the [Palomar registry](https://palomar-registry.org/)
from day one: `Challenge.lean` (statement), `Solution.lean` (proof),
`comparator.json`, and `formalization.yaml`. Run `bash scripts/verify-palomar.sh`
for the local checks; `bash scripts/verify-comparator.sh` runs the pinned
Comparator and NanoDa replay.

## Build

Requires [elan](https://github.com/leanprover/elan) with Lean 4.33.0:

```sh
lake update
lake build
```

## Sources

- Lloyd S. Shapley, "A Value for n-Person Games", 1953.
  (Contributions to the Theory of Games, vol. 2, Princeton University Press.)

## License

BSD-3-Clause. See LICENSE.
