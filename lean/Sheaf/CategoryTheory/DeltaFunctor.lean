/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import WeilConjectures.CategoryTheory.DeltaFunctor

/-!
# Cohomological delta-functors

Source: Stacks Project, Homology, Definitions 010Q, 010R, 010S
(blueprint: def-weil-pbc-delta-functor).

## Main definitions

* `CategoryTheory.CohomologicalDeltaFunctor`: additive functors with connecting maps,
  exactness, and naturality for short exact sequences.
* `CategoryTheory.CohomologicalDeltaFunctor.Hom`: compatible natural transformations.
* `CategoryTheory.CohomologicalDeltaFunctor.IsUniversal`: unique extension from degree zero.
-/
