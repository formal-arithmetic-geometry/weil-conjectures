/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Distinguished triangles for the translated-unit comparison

Source: Stacks Project, Tag 06YJ, mapping-cone exactness; translated-unit
comparison in lem-sc-derived-pullback-tensor-unit-shift.
(blueprint: lem-sc-derived-pullback-translated-unit-triangles).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- The translated-unit comparison can be normalized to preserve distinguished
localized homotopy triangles at degree one. No coherent integer-shift structure
or assertion about all derived triangles is assumed here.

Source: Stacks Project, Tag 06YJ; the mapping-cone part of the translated-unit
argument of lem-sc-derived-pullback-tensor-unit-shift.
(blueprint: lem-sc-derived-pullback-translated-unit-triangles).

Proof. Resolve the structure sheaf in degree zero by itself. Its translated
complex is K-flat, and its termwise pullback is the translated structure sheaf
on Z. Compare these representatives with derived pullback and the supplied
monoidal unit map to obtain e. Resolve a morphism by a morphism between K-flat
complexes and use its mapping cone, which is again K-flat. Termwise module
pullback is additive and identifies its cone with the cone of the pulled-back
map. Write translation as tensor with the translated structure sheaf, using the
first-variable Koszul map followed by the shifted left unitor. In these
coordinates the comparison of connecting maps is pullback of the inverse of
this rewrite, followed by the supplied inverse tensorator, e tensored with the
identity, and the target rewrite. The tensorator and unit equations give this
normalization for the supplied monoidal structure. Thus the three displayed
maps form a distinguished triangle. Every distinguished triangle in the derived
category is isomorphic to such a localized cone triangle. Naturality of the
rewrite, tensorator and e transports the assertion along this isomorphism.
Here the starting triangle is in the homotopy category: replace its complex
representatives by K-flat resolutions and compare the cone triangles after
localization. No assertion about arbitrary derived triangles is needed in this
lemma. Zero complexes and the empty scheme use the same cone and unitor equations. -/
theorem exists_derivedPullback_translatedUnit_triangles
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∀ T₀ : Triangle
          (HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
            (ComplexShape.up ℤ)),
        T₀ ∈ distTriang (HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) →
        let Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Y := DerivedCategory.Qh
        let T := Qh.mapTriangle.obj T₀
        Triangle.mk ((derivedPullback f).map T.mor₁) ((derivedPullback f).map T.mor₂)
          ((derivedPullback f).map T.mor₃ ≫
            ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y T.obj₁).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) T.obj₁) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj T.obj₁)).hom) ∈
          distTriang (schemeDerivedCategory Z) := by sorry

end AlgebraicGeometry
