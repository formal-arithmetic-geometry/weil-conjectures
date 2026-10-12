/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Comparing cones of smart cutoff inclusions with smart vertical windows

Source: blueprint thm-sp-double-complex-spectral-sequences, interval identification
in construction step 1; Stacks, Homology, Section 12.25 (tag 012X).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]


/-- Smart vertical intervals with a finite lower bound and an extended upper bound.
At top there is no upper cutoff; at bottom the interval is zero. -/
noncomputable def verticalInterval (a : ℤ) :
    EInt → (CochainComplex C ℕ ⥤ CochainComplex C ℕ) :=
  WithBotTop.rec 0 (verticalWindow a)
    (ComplexShape.embeddingUpNat.extendFunctor C ⋙
      (ComplexShape.embeddingUpIntGE a).truncGEFunctor C ⋙
      ComplexShape.embeddingUpNat.restrictionFunctor C)

instance verticalInterval_preservesZero (a : ℤ) (j : EInt) :
    (verticalInterval (C := C) a j).PreservesZeroMorphisms := by
  induction j using WithBotTop.rec with
  | bot => change (0 : CochainComplex C ℕ ⥤ CochainComplex C ℕ).PreservesZeroMorphisms
           infer_instance
  | coe b => exact inferInstanceAs ((verticalWindow (C := C) a b).PreservesZeroMorphisms)
  | top => dsimp only [verticalInterval, WithBotTop.rec_top]
           infer_instance

variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
    L.HasTotal (ComplexShape.up ℕ)]
  (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))

/-- Cones of cutoff inclusions compute smart intervals, including an infinite upper bound.
Source: blueprint thm-sp-double-complex-spectral-sequences, interval identification
in proof step 1; the finite-diagonal comparison of Stacks tag 012X.
(blueprint: lem-sp-double-complex-vertical-tower-comparison).

Proof: in each column, for finite j=b, the cone of the inclusion tau_{<a} K ->
tau_{<b} K is quasi-isomorphic to tau_{>=a} tau_{<b} K. For j=top use K in place
of tau_{<b} K. Obtain the comparison from the short exact sequence of the smart
lower truncation and its quotient: the projection from its cone to the quotient
is a quasi-isomorphism, and the quotient maps by a quasi-isomorphism to the smart
upper truncation. In the finite case canonical truncations commute for a<=b, so
this agrees with tau_{<b} tau_{>=a} K. These are the verticalInterval complexes.
All comparisons commute with horizontal differentials by functoriality of kernels
and cokernels. Keep these column cones integer-indexed: their vertical degree -1
may be nonzero and must not be discarded. Totalize them with their uniform lower
bound -1; the diagonals are still finite. Totalization preserves cones, with the
usual sign change on the shifted summand. It preserves these columnwise
quasi-isomorphisms: the cone of each
comparison has acyclic columns and a uniform lower bound; eliminate successive
horizontal components of a total cycle using vertical exactness. Each step decreases
the vertical degree, so the finite diagonal chase terminates. This is equally a
kernel-image chase in an arbitrary abelian category. Take homology of this zigzag
of quasi-isomorphisms. The cutoff and smart-window complexes themselves have
zero negative terms; extension and restriction lose no terms of those complexes.
The case a=b gives acyclic complexes. Negative bounds use extension by zero. All
integer homology degrees, including negative degrees, are included. The inequality
(a:EInt)<=j excludes j=bottom; the top case requires no eventual constancy of K. -/
theorem verticalTower_interval_homology_iso (a : ℤ) (j : EInt)
    (haj : (a : EInt) ≤ j) (n : ℤ) :
    Nonempty ((CochainComplex.mappingCone
      ((verticalTower K).map (homOfLE haj))).homology n ≅
      ((total (((verticalInterval a j).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).homology n) := by sorry

end HomologicalComplex₂
