/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension

/-!
# A finite smooth modification of a reduced curve

Source: Stacks Project, Varieties, Tags 0BXR and 0B8Y, as used in the proof of
Etale Cohomology, Tag 0A3Q (blueprint: lem-weil-pbc-reduced-curve-normalization).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A reduced separated finite-type scheme of dimension at most one over an algebraically
closed field admits a finite modification from a smooth separated finite-type scheme of
dimension at most one, which is an isomorphism over a dense open.
Source: Stacks Project, Tags 0BXR, 0B8Y and the proof of 0A3Q.
(blueprint: lem-weil-pbc-reduced-curve-normalization)

Proof:
1. For the empty scheme use the identity and the empty open. Otherwise finite type over a
field implies Noetherianity, hence finitely many irreducible components
(lem-weil-pbc-noetherian-finite-components). With their reduced closed subscheme structures,
the components are integral, separated, finite type, and of dimension zero or one. Their
inclusions are finite (lem-weil-pbc-closed-immersion-finite).
2. Normalize each one-dimensional component in its function field (def-sc-normalization).
By lem-sc-normalization-properties the map is finite, preserves dimension, and has smooth
source since an algebraically closed field is perfect. By lem-fin-dense-normal-open each
component has a nonempty normal open, over which its normalization is an isomorphism.
3. A zero-dimensional integral component is Spec k (lem-weil-pbc-zero-dim-integral-point).
Keep this component with the identity and the whole component as its normal open; this agrees
with its normalization and is smooth of dimension zero.
4. Take the finite disjoint union of these normalizations and their maps to X. Composition
and finite coproducts preserve finite morphisms (lem-weil-pbc-finite-composition,
lem-weil-pbc-finite-coproduct). The source is separated and finite type
(lem-weil-pbc-finite-over-separated-finite-type), smooth (lem-weil-pbc-smooth-coproduct), and
has dimension the maximum of the component dimensions, hence at most one.
5. Intersect each component's normal open with the complement of all the other components.
These are disjoint opens of X containing its respective generic points. Their union U is
therefore dense in X.
6. Over each of these opens the component inclusion is an isomorphism: it is a surjective
closed immersion into a reduced scheme, whose defining ideal is therefore zero. The other
components have empty preimage there. Thus the finite map is an isomorphism over each member
of this cover of U, and the inverses glue. This also explains the parenthetical construction:
one may take the disjoint union of the component normalizations as the witness. -/
theorem exists_finite_smooth_modification_of_reduced_curve
    {k : Type u} [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsReduced X]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (h_dim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X),
      IsSeparated (ν ≫ (X ↘ Spec (.of k))) ∧
      LocallyOfFiniteType (ν ≫ (X ↘ Spec (.of k))) ∧
      QuasiCompact (ν ≫ (X ↘ Spec (.of k))) ∧
      topologicalKrullDim Y ≤ 1 ∧ Smooth (ν ≫ (X ↘ Spec (.of k))) ∧
      IsFinite ν ∧ ∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (ν ∣_ U) :=
  sorry

end AlgebraicGeometry
