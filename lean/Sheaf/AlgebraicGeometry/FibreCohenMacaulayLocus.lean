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

/-! # Openness of the fibre Cohen-Macaulay locus

Source: Stacks Project, Tag 045U (1), (2).
(blueprint: lem-sbc-fibre-cohen-macaulay-locus-open)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- The fibre-stalk depth-equals-dimension locus of a flat locally finitely presented
morphism is open.

Source: Stacks Project, Tag 045U (1), (2), and Tag 00N8.
Proof: Cover the base and source by affine opens. On each affine chart the morphism
is given by a flat finitely presented algebra. Algebra, Tag 00RI gives openness of
its fibre Cohen-Macaulay locus. Fibres are locally of finite type over residue
fields and therefore locally Noetherian. In a Noetherian local ring, being
Cohen-Macaulay as a module over itself means that its depth equals its dimension;
the regular-sequence definition of depth and ring Krull dimension used here give
exactly this condition. The chartwise open sets agree on overlaps, since both
conditions depend only on the fibre local ring, and their union is the displayed
locus. An empty source has empty locus, so requires no exception.
(blueprint: lem-sbc-fibre-cohen-macaulay-locus-open) -/
theorem isOpen_fibre_depth_eq_ringKrullDim
    {X T : Scheme.{u}} (f : X ⟶ T) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen {y : X |
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))} := by sorry

end AlgebraicGeometry
