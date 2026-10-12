/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import Sheaf.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Quasi-finite morphisms are locally quasi-finite and quasi-compact

Source: literature/blueprint/master/blueprint/sec-nagata-compactification/
sk-prop-nagata-sketch-zmt/pqf-lem-qf-locqf-qc.md, node pqf-lem-qf-locqf-qc,
order 200 (blueprint: pqf-lem-qf-locqf-qc).
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism is quasi-finite exactly when it is locally quasi-finite and
quasi-compact, in the sense of Stacks Tag 01TD.

Source: Stacks Project, Morphisms of Schemes, Tag 01TJ
(blueprint: pqf-lem-qf-locqf-qc).

Proof:
1. Suppose `f` is quasi-finite. By `pqf-def-quasifinite` and
   `def-weil-pbc-scheme-conventions`, it is locally of finite type and
   quasi-compact, and every point is isolated in its fibre. Choose affine
   neighbourhoods of a source point and its image. Apply
   `lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs` to obtain
   the finite-type affine quasi-finite-at-prime condition. This gives
   quasi-finiteness at every point, hence local quasi-finiteness.
2. Conversely, `lem-weil-pbc-lqf-locally-finite-type` gives local finite
   type from local quasi-finiteness. Together with quasi-compactness this
   gives finite type by `def-weil-pbc-scheme-conventions`. Apply
   `lem-weil-pbc-quasi-finite-at-point-isolated` at each point to obtain
   isolated fibre points. The definition `pqf-def-quasifinite` now gives
   quasi-finiteness.
-/
theorem isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact
    {X S : AlgebraicGeometry.Scheme.{v}} (f : X ⟶ S) :
    IsQuasiFinite f ↔ IsLocallyQuasiFinite f ∧ AlgebraicGeometry.QuasiCompact f := by
  sorry

end AlgebraicGeometry.Scheme.Hom
