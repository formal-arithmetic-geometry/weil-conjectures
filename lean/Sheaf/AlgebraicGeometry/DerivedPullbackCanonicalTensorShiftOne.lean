/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
/-! # Pullback relative to canonical tensor shifts
Source: Stacks Project, Tag 08EU; parent representative construction step 2.
(blueprint: lem-sc-derived-pullback-canonical-tensor-shift-one).
-/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
/-- Pullback exact shift and its inverse-tensorator square relative to canonical tensor shifts.
Source: Stacks Tag 08EU, proof, with the translated-unit argument of the parent plan.
(blueprint: lem-sc-derived-pullback-canonical-tensor-shift-one).

Proof. Compute pullback on K-flat resolutions by termwise tensor pullback, which
preserves mapping-cone triangles. Identify translation with tensoring by the translated
unit using the Koszul comparison. Apply the supplied inverse tensorator and unit
isomorphism to transport this expression to the target. Iterate the degree-one
comparison and its inverse for all integers. Tensorator associativity gives addition
coherence and the unit equations give zero coherence. The mapping-cone comparison gives
exactness. Expand the inverse-tensorator square at shift one: both paths identify the
same translated tensor pullback, by tensorator associativity and the unit equations.
These equalities descend along the K-flat localization. Zero complexes and empty
schemes satisfy the same equations. Stacks supplies geometric exactness; transport
for the supplied monoidal structure is the agent expansion of the parent plan. -/
theorem derivedPullback_canonicalTensorShift_one
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    letI := schemeCanonicalTensorShift Y
    letI := schemeCanonicalTensorShift Z
    letI : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
      fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
    letI : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ :=
      fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
    ∃ (sF : (derivedPullback f).CommShift ℤ),
      letI := sF
      (derivedPullback f).IsTriangulated ∧
      (∀ (M : schemeDerivedCategory Y)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ),
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := ((Functor.OplaxMonoidal.δNatTrans (derivedPullback f)).flipApp M)
        ((tensorRight M ⋙ derivedPullback f).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫
            ((derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M)).commShiftIso
              (1 : ℤ)).hom.app K) := by sorry

end AlgebraicGeometry
