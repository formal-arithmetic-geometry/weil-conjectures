/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Exact shifts compatible with a specified derived monoidal pullback

Source: Stacks Project, Tags 0A9U and 0A9S, equation-compare-with-pullback.
(blueprint: lem-sc-derived-monoidal-pullback-unital-shift).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Simultaneous exact tensor and pullback shifts, natural in the fixed tensor
factor on both schemes and compatible with the right unitor on the base.
Source: Stacks Project, Tags 0A9U and 0A9S, equation-compare-with-pullback;
representative-complex step 1 of lem-sc-pinned-projection-counit-exact-shift.
(blueprint: lem-sc-derived-monoidal-pullback-unital-shift).

Proof. Compute derived tensor and pullback on K-flat representatives. Translation
in the first tensor variable has the Koszul comparison, natural in the second
factor, and tensor of a cone is the cone of the tensor map. These comparisons
descend through localization, including their zero and addition identities, so
all tensorRight functors are exact and their maps commute with shifts on both
schemes. The complex right unitor identifies the translation comparison for
K tensor O_Y with translation of K, and this equation descends as well. Compute
pullback by termwise tensor pullback of K-flat resolutions: it takes cones to cones.
For the supplied strong monoidal structure, choose the pullback comparison
simultaneously with these tensor comparisons by expressing translation as tensor
with the translated unit, then applying its tensorator and unit isomorphism.
Associativity of the tensorator gives addition coherence, and its unit equations
give zero coherence and the right-unitor equation. The inverse tensorator then
commutes with translation in its varying first factor. The comparison identifies
the images of representative cone triangles, proving exactness for the chosen
pullback shift. Descend all equations through K-flat localization. No direct
image, adjunction, projection isomorphism, or map to the unit is used. Zero tensor
factors, empty schemes and translation by zero satisfy the same unit equations. -/
theorem exists_derivedMonoidalPullback_unitalShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sL : (derivedPullback f).CommShift ℤ)
      (sY : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ)
      (sZ : ∀ M : schemeDerivedCategory Z, (tensorRight M).CommShift ℤ),
      letI := sL
      letI := sY
      letI := sZ
      (derivedPullback f).IsTriangulated ∧
      (∀ M : schemeDerivedCategory Z, (tensorRight M).IsTriangulated) ∧
      (∀ {M N : schemeDerivedCategory Y} (b : M ⟶ N),
        NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Y)).flip.map b) ℤ) ∧
      (∀ {M N : schemeDerivedCategory Z} (b : M ⟶ N),
        NatTrans.CommShift ((curriedTensor (schemeDerivedCategory Z)).flip.map b) ℤ) ∧
      (∀ M : schemeDerivedCategory Y,
        NatTrans.CommShift (F₁ := tensorRight M ⋙ derivedPullback f)
          (F₂ := derivedPullback f ⋙ tensorRight ((derivedPullback f).obj M))
          ((Functor.OplaxMonoidal.δNatTrans (derivedPullback f)).flipApp M) ℤ) ∧
      NatTrans.CommShift (rightUnitorNatIso (schemeDerivedCategory Y)).hom ℤ := by sorry

end AlgebraicGeometry
