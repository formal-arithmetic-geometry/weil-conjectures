/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Sheaf.AlgebraicGeometry.SteinFactorizationAffine

/-!
# Geometrically connected fibres over a normal base

Source: Stacks Project, More on Morphisms, Tag 0AY8, label
`lemma-geometrically-connected-fibres-towards-normal`
(blueprint: lem-trf-proper-normal-geometric-connectedness).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a proper map to an integral normal scheme, reducedness, dominance of every
component, and trivial generic-fibre global functions imply that the canonical
structure-sheaf map is an isomorphism and every fibre is geometrically connected.
`ConnectedSpace` in `GeometricallyConnected` includes nonemptiness.

Source: Stacks Project, More on Morphisms, Tag 0AY8,
`lemma-geometrically-connected-fibres-towards-normal`.
(blueprint: lem-trf-proper-normal-geometric-connectedness)

Proof, following the six steps of the node:
1. Work on a nonempty affine open `U = Spec A` of `S`, containing `ξ`. Its inverse
   image `Y` is proper over `U` and qcqs by `lem-weil-pbc-proper-fp-permanence`
   and `lem-weil-pbc-qcqs-over-affine`, and is reduced. Integralness makes `A` a
   domain. By `lem-weil-pbc-spec-domain-stalks-function-field`, `κ(ξ)` is its
   fraction field `K`, and the generic fibre is unchanged by restriction to `U`.
2. Each local ring of `A` is a local ring of `S`, hence a normal domain.
   The normal-ring criterion in
   `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions` makes `A`
   integrally closed in `K`; the domain `A` has just the minimal prime zero.
3. `lem-weil-pbc-stein-factorization-affine` factors `Y` through `Spec B`, where
   `B = Γ(Y, O_Y)`, the map `A → B` is integral, and `Y → Spec B` is proper
   with geometrically connected fibres. Restriction to the generic fibre and
   the structural isomorphism on its global sections give an `A`-map `B → K`.
4. This map is injective: a section vanishing on the generic fibre vanishes at
   every component generic point, by the dominance hypothesis. Components cover
   `X` by `lem-sc-irreducible-components-cover` and have generic points by
   `lem-sc-scheme-sober`. The zero-residue locus is closed, so all residues
   vanish. The section is nilpotent by
   `lem-weil-pbc-qc-scheme-vanishing-section-nilpotent`, hence zero by reducedness.
5. Every element of `B` maps to an element of `K` integral over `A`, hence to an
   element of `A`. Injectivity of `B → K` now makes `A → B` an isomorphism.
   This is the canonical structure-sheaf map on every nonempty affine open;
   on the empty open both rings are zero. The inverse maps commute with
   restriction by uniqueness and glue on affine covers to an inverse sheaf map.
6. In the Stein factorization, `Spec B → Spec A` is consequently an isomorphism.
   The geometrically connected fibres of its first map are therefore those of
   `f`. Restriction to an affine neighbourhood of each `s` and arbitrary
   extension of `κ(s)` proves the asserted geometric connectedness, including
   nonemptiness. No Noetherian or finite-presentation hypothesis is used. -/
theorem proper_normal_geometric_connectedness
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsIntegral S] [IsReduced X]
    (ξ : S) (hξ : IsGenericPoint ξ (Set.univ : Set S))
    (hnormal : ∀ x : S,
      IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x))
    (hgeneric : ∀ Z ∈ irreducibleComponents X,
      ∀ η : X, IsGenericPoint η Z → f η = ξ)
    (hsections : IsIso (f.fiberToSpecResidueField ξ).appTop) :
    IsIso f.toLRSHom.toHom.c ∧
      ∀ s : S, GeometricallyConnected (f.fiberToSpecResidueField s) := by
  sorry

end AlgebraicGeometry
