/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.KrullDimension

/-!
# Dimension of a quasi-separated algebraic space on an étale atlas

Source: Stacks Project, Decent Spaces, Tags 0A4J and 03JX; Properties of Spaces,
Tags 04N5 and 04N6 (blueprint: lem-sfb-quasiseparated-space-atlas-dimension).

The diagonal hypothesis is tested on schemes. Dimensions take values in `WithBot ℕ∞`,
including the empty space and infinite dimension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A surjective étale scheme atlas computes the topological Krull dimension of a
quasi-separated algebraic space over a field.
Source: Stacks, Tags 0A4J(1),(2), 03JX, 04N5 and 04N6
(blueprint: lem-sfb-quasiseparated-space-atlas-dimension).

Proof: set both base schemes in lem-sfb-space-etale-atlas-topological-dimension to
`Spec k`, with the identity base-change map. The presheaf `P = Y ×_(Spec k) Spec k`
is canonically `Y`: on each scheme test the projection sends `(y,b)` to `y`, and
its inverse sends `y` to `(y,f(y))`. These natural transformations are inverse
(def-trf-algebraic-space). The atlas of `Y` is therefore an atlas of `P`, with the
same scheme-test projections, and the quasi-compact diagonal is the given one.
Apply lem-sfb-space-etale-atlas-topological-dimension to obtain `dim |P| = dim |U|`.
The inverse natural transformations identify field-valued point classes and all
étale scheme-source maps, hence the final topologies of def-a1-space-point-topology.
They induce a homeomorphism `|P| ≃ₜ |Y|`; use
lem-weil-pbc-homeomorphism-krull-dimension to replace `dim |P|` by `dim |Y|`.
No finiteness condition is used, so this includes infinite and empty dimensions. -/
theorem topologicalKrullDim_eq_atlas_of_quasiSeparated
    (k : Type u) [Field k] (Y : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)))
    (U : Over (Spec (CommRingCat.of k))) (a : yoneda.obj U ⟶ Y.obj.obj)
    (ha : IsEtale a) (hs : IsSurjective a) :
    topologicalKrullDim (Point Y.obj.obj) = topologicalKrullDim U.left := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
