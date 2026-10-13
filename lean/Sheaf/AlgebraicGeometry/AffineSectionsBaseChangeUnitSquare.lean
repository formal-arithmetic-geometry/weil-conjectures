/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap

/-! # Affine sections of the base-change unit square

Source: Stacks Project, cohomology.tex, Tags 0D5T and 08HY;
perfect.tex, Tag 0AA7. (blueprint: lem-pc-affine-sections-base-change-unit-square).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The right-adjoint base-change unit square after taking affine sections.
This is an identity of maps over R, for arbitrary E. It constructs no extension
isomorphism and requires no quasi-coherence. Only the canonical pullback unit
is used: the passage to all L and m is a separate naturality argument.
Source: Stacks, cohomology.tex, Tag 08HY (remark-base-change) and
Tag 0D5T (lemma-derived-pushforward-composition); perfect.tex, Tag 0AA7.
(blueprint: lem-pc-affine-sections-base-change-unit-square).
Proof:
1. Expand schemeDerivedBaseChangeMap as the adjunct of the canonical
pullback-composition comparison followed by the pullback of the counit of f.
Transpose through Lg* and through Lg_X*. Naturality of their units and the
triangle identities cancel the units and counits of f and f'. The remaining
identity is the unit description of base change in the commuting square.
2. Apply sections. The normalized comparisons b, d, and r identify the
composed direct images with their sections, without changing the underlying
sections on sheaves. Their displayed right-derived-unit equations specify
these identifications on the homotopy categories.
3. Both maps now compute the same underived identity on K-injective models.
The identity assumptions ht, hz, hv, hs identify the scalar actions. The
normalizations hb, hd, hr, hc and right-derived uniqueness identify the two
maps on the full derived categories, giving the displayed equation for E.
No inverse of the base-change map is used, so flatness and Tor independence
are unnecessary; the equation also holds for E=0 and identity base change. -/
theorem affineSectionsBaseChange_unit_square
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R)
    (t : RingedSpace.moduleDirectImage (f).toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅ affineGlobalSections (f))
    (b : schemeDerivedDirectImage (f) ⋙
        affineDerivedGlobalSections (𝟙 (Spec R)) ≅ affineDerivedGlobalSections (f))
    (ht : ∀ (M : SheafOfModules.{u} (moduleRings (X).toRingedSpace))
        (x : (affineGlobalSections (f)).obj M), (t.hom.app M) x = x)
    (hb : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (X).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage (f).toLRSHom.toShHom)
          (affineGlobalSections (𝟙 (Spec R)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
          ((schemeDerivedDirectImage (f)).obj (DerivedCategory.Qh.obj J)) ≫
        b.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((t.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (f)).rightDerivedFunctorUnit.app J ≫
        (affineGlobalSectionsDerivedIso (f)).hom.app (DerivedCategory.Qh.obj J))
    (z : RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec B)) ≅ affineGlobalSections (pullback.snd f g))
    (d : schemeDerivedDirectImage (pullback.snd f g) ⋙
        affineDerivedGlobalSections (𝟙 (Spec B)) ≅ affineDerivedGlobalSections (pullback.snd f g))
    (hz : ∀ (M : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : (affineGlobalSections (pullback.snd f g)).obj M), (z.hom.app M) x = x)
    (hd : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom)
        (affineGlobalSections (𝟙 (Spec B)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec B))).hom.app
          ((schemeDerivedDirectImage (pullback.snd f g)).obj (DerivedCategory.Qh.obj J)) ≫
        d.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map
        ((z.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (pullback.snd f g)).rightDerivedFunctorUnit.app J ≫
        (affineGlobalSectionsDerivedIso (pullback.snd f g)).hom.app (DerivedCategory.Qh.obj J))
    (v : RingedSpace.moduleDirectImage g.toLRSHom.toShHom ⋙
        affineGlobalSections (𝟙 (Spec R)) ≅
      affineGlobalSections (𝟙 (Spec B)) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (r : schemeDerivedDirectImage g ⋙ affineDerivedGlobalSections (𝟙 (Spec R)) ≅
      affineDerivedGlobalSections (𝟙 (Spec B)) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory)
    (hv : ∀ (M : SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (x : (affineGlobalSections (𝟙 (Spec B))).obj M), (v.hom.app M) x = x)
    (hr : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage g.toLRSHom.toShHom)
          (affineGlobalSections (𝟙 (Spec R)))).app J ≫
        (affineGlobalSectionsDerivedIso (𝟙 (Spec R))).hom.app
          ((schemeDerivedDirectImage g).obj (DerivedCategory.Qh.obj J)) ≫
        r.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((v.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (𝟙 (Spec B)) ⋙
          ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctorUnit.app J ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
            (affineGlobalSections (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)) ≪≫
          Functor.isoWhiskerRight (affineGlobalSectionsDerivedIso (𝟙 (Spec B)))
            (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory).hom.app
          (DerivedCategory.Qh.obj J))
    (E : schemeDerivedCategory X)
    (s : RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom ⋙
        affineGlobalSections f ≅
      affineGlobalSections (pullback.snd f g) ⋙
        ModuleCat.restrictScalars.{u} (affineBaseRingMap g))
    (c : schemeDerivedDirectImage (pullback.fst f g) ⋙
        affineDerivedGlobalSections f ≅
      affineDerivedGlobalSections (pullback.snd f g) ⋙
        (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory)
    (hs : ∀ (F : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
        (x : (affineGlobalSections (pullback.snd f g)).obj F),
      (s.hom.app F) x = x)
    (hc : ∀ J : HomotopyCategory
        (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (ComplexShape.up ℤ),
      (Functor.rightDerivedFunctorCompUnit
          (RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom)
          (affineGlobalSections f)).app J ≫
        (affineGlobalSectionsDerivedIso f).hom.app
          ((schemeDerivedDirectImage (pullback.fst f g)).obj (DerivedCategory.Qh.obj J)) ≫
        c.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((s.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
        (affineGlobalSections (pullback.snd f g) ⋙
          ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).rightDerivedFunctorUnit.app J ≫
        (affineBaseChangedSectionsDerivedIso f g).hom.app (DerivedCategory.Qh.obj J)) :
    (affineDerivedGlobalSections (𝟙 (Spec R))).map
        ((canonicalPullbackAdjunction g).unit.app ((schemeDerivedDirectImage f).obj E)) ≫
      r.hom.app ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≫
      (ModuleCat.restrictScalars.{u} (affineBaseRingMap g)).mapDerivedCategory.map
        ((affineDerivedGlobalSections (𝟙 (Spec B))).map
            (schemeDerivedBaseChangeMap f (pullback.snd f g) g
              (pullback.fst f g) pullback.condition E) ≫
          d.hom.app ((derivedPullback (pullback.fst f g)).obj E)) =
      b.hom.app E ≫ (affineDerivedGlobalSections f).map
          ((canonicalPullbackAdjunction (pullback.fst f g)).unit.app E) ≫
        c.hom.app ((derivedPullback (pullback.fst f g)).obj E) := by sorry

end AlgebraicGeometry
