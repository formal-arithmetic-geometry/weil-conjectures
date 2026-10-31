/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification

/-! # Local rings at the boundary of a split nodal subcurve

Source: Stacks Project, Curves, Tag 0E38, completed-local-ring calculation.
(blueprint: lem-trf-split-nodal-boundary-local-rings).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A pure reduced subcurve passing through a split node and meeting its complementary
closure selects one branch. Its local ring is regular and the intersection stalk is a field.

Source: Stacks Project, Curves, Tag 0E38, proof paragraphs 2--3, with Varieties Tag 0C3V
for reduced completed component quotients.
(blueprint: lem-trf-split-nodal-boundary-local-rings).

Proof: Let A be the ambient local ring, F its residue field, and H its completion.
The subcurve and the complementary closure are unions of complementary components.
Boundary membership supplies an incident component in each union. Every minimal prime of A
lifts to a prime of H by faithful flatness. In H = F[[u,v]]/(uv), the only primes are the two
axis ideals and the maximal ideal: an axis quotient is a dimension-one power series local
domain. Thus A has exactly two incident minimal primes p,q, one in each union; neither is
zero. The completed quotients A/p and A/q are reduced of dimension one by the normalization
and completion theorem for local algebraic curves. Completion of a quotient identifies
them with H/pH and H/qH. The prime list shows that the nonzero radical ideals pH,qH are the
two distinct axis ideals; faithful-flat contraction excludes zero and equality. Their sum
is the maximal ideal of H, and contraction gives p+q equal to the maximal ideal of A.
The actual closed-immersion kernels are p and q because both subschemes are reduced unions
of the specified components. Their intersection stalk is therefore A/(p+q) = F.
The completed subcurve local ring is an axis quotient, hence F[[t]], a regular local ring.
Regularity descends from completion.
This is pointwise; neither global nodality nor any assertion about points away from y is used.
-/
theorem split_nodal_boundary_local_rings
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hY : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = 1)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hboundary : i y ∈ Set.range (Scheme.openComplementOfIsClosedImmersion i).ι.imageι)
    (hcompletion : Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk (i y)))
        (X.presheaf.stalk (i y)) ≃+*
        (MvPowerSeries (Fin 2) (X.residueField (i y)) ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2)
            (X.residueField (i y))) * MvPowerSeries.X 1}))) :
    IsRegularLocalRing (Y.presheaf.stalk y) ∧
      ∀ t : pullback (C := Scheme.{u}) i
          (Scheme.openComplementOfIsClosedImmersion i).ι.imageι,
        pullback.fst i (Scheme.openComplementOfIsClosedImmersion i).ι.imageι t = y →
        IsField ((pullback (C := Scheme.{u}) i
          (Scheme.openComplementOfIsClosedImmersion i).ι.imageι).presheaf.stalk t) := by
  sorry

end AlgebraicGeometry
