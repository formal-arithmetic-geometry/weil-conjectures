/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.GrothendieckHypercoverComparisonCocone

/-! # The colimit of the explicit hypercover comparison maps -/

@[expose] public section

universe u' u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

local instance : HasColimitsOfSize.{u, u + 1} A :=
  hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A

/-- Finite refinement makes the positive-degree bottom comparison a colimit isomorphism.
Source: Stacks Project, Hypercoverings, Tag 01H0, first proof; the finite staircase
argument of blueprint lem-sc-hypercover-bottom-refinement-descent.
(blueprint: lem-weil-pbc-grothendieck-hypercover-bottom-colimit).

Proof: the comparison cocone is already constructed from an injective resolution
and the two augmentations of its section bicomplex. Its top augmentation is a
quasi-isomorphism by injective-row acyclicity. To analyze the bottom inclusion,
filter the first-quadrant total complex by resolution degree. For a fixed total
positive degree r, only the finite rectangle through r + 1 can contribute. Exactness of the
injective resolution is local on each hypercover constituent. Finite refinement
of its matching covers supplies the local lifting diagrams for these finitely
many differentials. Descending through the rectangle removes the positive
resolution-degree components, proving surjectivity of the bottom comparison
after refinement. Applying the same staircase to a bounding cochain proves
that its kernel vanishes after refinement. These arguments are statements about
images and kernels in A, using covers and finite direct sums, rather than chosen
global elements of A. Common refinements and homotopy equalization make the
index filtered; AB5 turns these local image/kernel statements into an
isomorphism on the filtered colimit. The comparison from that colimit is exactly
the displayed colimit.desc, since its components are the already constructed
bottom-row comparison maps. Degree zero is proved separately in
GrothendieckHypercoverZero. On the empty scheme all section objects are zero. -/
theorem isIso_colimit_comparison_positive (F : Sheaf X.smallEtaleTopology A) (q : ℕ) :
    IsIso (colimit.desc (homotopyCohomologyDiagram A F (q + 1))
      (comparisonCocone A F (q + 1))) := by
  sorry

end AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck
