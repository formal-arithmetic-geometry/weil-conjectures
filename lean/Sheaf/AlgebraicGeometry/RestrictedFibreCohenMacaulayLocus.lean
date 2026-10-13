/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.RingTheory.Depth

/-! # Openness of the fibre Cohen-Macaulay locus over a base open

Source: Stacks Project, Tag 045U.
(blueprint: lem-sbc-restricted-fibre-cohen-macaulay-locus-open)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- The Cohen-Macaulay fibre-stalk locus is open over a flat finitely presented restriction.

Source: Stacks Project, Tag 045U (1), (2), with Cohen-Macaulayness expressed by depth.
Proof: Form the base restriction `f ∣_ U`. For each point of its source, the
restriction pullback square and the residue-field isomorphism of the open immersion
identify its fibre with the original fibre. Their stalks are isomorphic as local
rings, preserving depth and Krull dimension. The restricted fibres are locally of
finite type over fields, hence locally Noetherian. For these rings equality of depth
and Krull dimension is exactly Cohen-Macaulayness. Tag 045U (1), (2) says that this
locus in the restricted source is open. The source restriction inclusion is an open
immersion, and its image is precisely the set displayed below. Its image is open in X.
For an empty U or X this set is empty, which is open.
(blueprint: lem-sbc-restricted-fibre-cohen-macaulay-locus-open) -/
theorem isOpen_fibre_depth_eq_ringKrullDim_over_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] :
    IsOpen {y : X | f y ∈ U ∧
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))} := by sorry

end AlgebraicGeometry
