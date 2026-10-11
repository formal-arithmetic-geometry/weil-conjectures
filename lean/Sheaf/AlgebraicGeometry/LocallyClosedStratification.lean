/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.Topology.Stratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Finite locally closed stratifications of schemes

Source: Stacks Project, Topology, Definition 09XZ, with finiteness added and scheme
immersions realizing the parts (blueprint: def-constructible-stratification).
-/

@[expose] public section

universe w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite partition into locally closed subsets, with a scheme immersed into `X`
realizing each subset. No constructibility or closure-incidence condition is imposed.
Source: Stacks Project, Tag 09XZ (blueprint: def-constructible-stratification). -/
structure LocallyClosedStratification (X : Scheme.{w}) extends Topology.Stratification X where
  /-- The schemes realizing the strata. -/
  domain : Fin n → Scheme.{w}
  /-- The morphisms realizing the strata. -/
  immersion : ∀ i : Fin n, domain i ⟶ X
  /-- Every stratum morphism is an immersion. -/
  isImmersion : ∀ i : Fin n, IsImmersion (immersion i)
  /-- Its set-theoretic image is the corresponding part. -/
  range_immersion : ∀ i : Fin n, Set.range (immersion i) = stratum i

end AlgebraicGeometry.Scheme
