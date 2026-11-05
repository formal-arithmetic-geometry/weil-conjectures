/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Order.JordanHolder
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Composition series of representations

Let `ρ` be a representation of a group `W` on a vector space `V` over a field `k`. A *composition
series* of `ρ` is a finite chain `0 = V₀ ⋖ V₁ ⋖ ⋯ ⋖ V_t = V` of subrepresentations, each covering
the previous one; equivalently every quotient `V_i / V_{i-1}` is irreducible
(`Subrepresentation.isIrreducible_subquotient_iff`). These quotients are its *composition
factors*.

## Main definitions

- `Subrepresentation.subquotientOrderIso`: the subrepresentations of `S / U` are the
  subrepresentations between `U` and `S`.
- `Representation.CompositionSeries`: a composition series of `ρ`, with its composition factors
  `Representation.CompositionSeries.factor`.
- `Representation.CompositionSeries.semisimplification`: the direct sum of the composition factors.

## Main results

- `Representation.CompositionSeries.isIrreducible_factor`: the composition factors are irreducible.
- `Representation.exists_compositionSeries`: a finite-dimensional representation has a composition
  series.
- `Representation.CompositionSeries.jordanHolder`: two composition series have the same factors,
  up to permutation and isomorphism.
- `Representation.CompositionSeries.nonempty_semisimplification_equiv`: the semisimplification does
  not depend on the composition series.

## Blueprint

- `def-mg-weil-composition-series`: composition series and composition factors.
- `lem-mg-composition-series-exists`, `lem-mg-jordan-holder`: existence, and Jordan–Hölder.
- `def-mg-weil-semisimplification`, `lem-mg-semisimplification-independent`: the
  semisimplification.
-/

@[expose] public section

open Set

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

end Subrepresentation

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  (ρ : Representation k W V)

namespace CompositionSeries

variable {ρ} (s : ρ.CompositionSeries)

end CompositionSeries

section DirectSum

open DirectSum

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {V' : ι → Type*}
  [∀ i, AddCommGroup (V' i)] [∀ i, Module k (V' i)] {U' : κ → Type*} [∀ j, AddCommGroup (U' j)]
  [∀ j, Module k (U' j)] {ρs : ∀ i, Representation k W (V' i)}
  {σs : ∀ j, Representation k W (U' j)}

end DirectSum

open DirectSum

namespace CompositionSeries

variable {ρ} (s : ρ.CompositionSeries)

end CompositionSeries

end Representation
