/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Translation expressed using the translated tensor unit

Source: Stacks Project, Tag 08EU, exactness in the proof; Tag 06YH, total tensor
translation. This is the translated-unit construction in the parent plan.
(blueprint: lem-sc-derived-pullback-tensor-unit-shift).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry

/-- Pullback translation induced by an isomorphism on the translated unit. The
source translation is rewritten as tensor with the translated unit; the inverse
tensorator and `e` transport it to the target, where the same canonical comparison
rewrites it as translation again.
Source: the translated-unit argument of the parent plan, Stacks Project, Tag 08EU.
(blueprint: lem-sc-derived-pullback-tensor-unit-shift). -/
noncomputable def derivedPullbackTensorUnitShiftIso {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (K : schemeDerivedCategory Y) :
    (derivedPullback f).obj (K⟦(1 : ℤ)⟧) ≅ ((derivedPullback f).obj K)⟦(1 : ℤ)⟧ :=
  (derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y K).symm ≪≫
    asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
      ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) K) ≪≫
    tensorIso e (Iso.refl _) ≪≫ schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj K)

/-- The translated-unit formula admits a coherent exact pullback shift. This only
asserts the formula for pullback translation itself, not the tensorator square.
Source: Stacks Project, Tag 08EU, proof (exactness); Tags 06YH and 06YJ,
K-flat tensor and pullback; the translated-unit argument of the parent plan.
(blueprint: lem-sc-derived-pullback-tensor-unit-shift).

Proof. Represent the unit by the structure sheaf in degree zero and its translate
by that complex translated by one. Termwise tensor pullback of this K-flat complex
is the structure sheaf of Z translated by one. The comparison with derived pullback
and the supplied monoidal unit isomorphism give e. On a K-flat complex P, rewrite
P[1] as O_Y[1] tensor P using the first-variable Koszul map and the left unitor.
Apply the supplied inverse tensorator and e, then undo this rewrite over Z. This
is the displayed composite. Naturality follows from the tensorator, Koszul map
and left unitor. Iterate this comparison for positive integers, use its inverse
for negative integers and the canonical zero comparison at zero. Associativity
of composition and the shift addition isomorphisms give the addition equations;
the zero equations are the unitor equations. Termwise tensor pullback takes the
mapping cone of a map of K-flat resolutions to its mapping cone. The translated
unit comparison identifies the third map, so the induced triangle is
distinguished. Descend through the K-flat localization; every distinguished
triangle is isomorphic to one of these cone triangles. This proves exactness for
this shift structure. The formula and coherence hold also for the zero complex
and the zero category on an empty scheme. No choice from this existence theorem
is used to define any data: the comparison above was constructed explicitly. -/
theorem exists_derivedPullback_tensorUnitShift
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ (sF : (derivedPullback f).CommShift ℤ)
      (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧),
      letI := sF
      (derivedPullback f).IsTriangulated ∧
      ∀ K : schemeDerivedCategory Y,
        ((derivedPullback f).commShiftIso (1 : ℤ)).hom.app K =
          (derivedPullbackTensorUnitShiftIso f e K).hom := by sorry

end AlgebraicGeometry
