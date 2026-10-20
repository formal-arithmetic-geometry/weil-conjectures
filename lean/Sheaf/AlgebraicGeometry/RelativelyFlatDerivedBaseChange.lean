/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Derived base change for a relatively flat module

Source: Weil conjectures blueprint, sec-picard-framework/sk-thm-picard-semicon,
lemma lem-pc-rf-base-change-flat-module (blueprint: lem-pc-rf-base-change-flat-module).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Compare single objects with the fixed small model of the derived category.
private def singleModelIso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (G : X.Modules) :
    (schemeDerivedCategoryEquiv.{w} X).functor.obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≅
      (DerivedCategory.singleFunctor.{u} X.Modules 0).obj G :=
  (schemeDerivedCategoryEquiv X).functor.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app G) ≪≫
    (qCompSchemeDerivedCategoryEquivFunctor X).app _ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ.{u} X.Modules 0).app G).symm

-- Both direct images are computed by the same K-injective resolution.
private theorem directImageModelIso
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    Nonempty ((schemeDerivedCategoryEquiv.{w} S).functor.obj
        ((schemeDerivedDirectImage f).obj E) ≅
      (Scheme.Modules.derivedPushforward f).obj
        ((schemeDerivedCategoryEquiv.{w} X).functor.obj E)) := by
  let Q := DerivedCategory.Q
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let P := Q.objPreimage E
  let I := CochainComplex.kInjectiveResolutionFunctor.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let η := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  have : QuasiIso (η.app P) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ P).2
  obtain ⟨a⟩ := RingedSpace.derivedModuleDirectImage_computed_by_resolution
    f.toLRSHom.toShHom (η.app P)
  let b := (schemeDerivedCategoryEquiv X).functor.mapIso (Q.objObjPreimageIso E).symm ≪≫
    (qCompSchemeDerivedCategoryEquivFunctor X).app P ≪≫
    asIso ((DerivedCategory.Q (C := X.Modules)).map (η.app P))
  let F := Scheme.Modules.pushforward f
  have : (show CochainComplex X.Modules ℤ from I.obj P).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj _ P
  exact ⟨(schemeDerivedCategoryEquiv S).functor.mapIso
      ((schemeDerivedDirectImage f).mapIso (Q.objObjPreimageIso E).symm ≪≫ a) ≪≫
    (qCompSchemeDerivedCategoryEquivFunctor S).app _ ≪≫
    (F.rightDerivedFunctorObjQIso (I.obj P)).symm ≪≫
    F.rightDerivedFunctor.mapIso b.symm⟩

private def pullbackModelIso
    {S T : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (E : schemeDerivedCategory S) :
    (schemeDerivedCategoryEquiv.{w} T).functor.obj ((derivedPullback g).obj E) ≅
      (Scheme.Modules.derivedPullback g).obj
        ((schemeDerivedCategoryEquiv.{w} S).functor.obj E) := by
  rw [derivedPullback_def]
  exact (schemeDerivedCategoryEquiv T).counitIso.app _

private theorem sourceModelIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    Nonempty ((schemeDerivedCategoryEquiv.{w} T).functor.obj
        ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G))) ≅
      (Scheme.Modules.derivedPullback g).obj ((Scheme.Modules.derivedPushforward f).obj
        ((DerivedCategory.singleFunctor.{u} X.Modules 0).obj G))) := by
  obtain ⟨a⟩ := directImageModelIso f
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)
  exact ⟨pullbackModelIso g _ ≪≫ (Scheme.Modules.derivedPullback g).mapIso
    (a ≪≫ (Scheme.Modules.derivedPushforward f).mapIso (singleModelIso X G))⟩

private theorem targetModelIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    Nonempty ((schemeDerivedCategoryEquiv.{w} T).functor.obj
        ((schemeDerivedDirectImage (pullback.snd f g)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))) ≅
      (Scheme.Modules.derivedPushforward (pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor.{u} (pullback f g).Modules 0).obj
          ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))) := by
  obtain ⟨a⟩ := directImageModelIso (pullback.snd f g)
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))
  exact ⟨a ≪≫ (Scheme.Modules.derivedPushforward (pullback.snd f g)).mapIso
    (singleModelIso (pullback f g) _)⟩

private theorem moduleModelBaseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    (G : X.Modules) [G.IsQuasicoherent] (hflat : G.IsFlatOver f) (g : T ⟶ S) :
    Nonempty ((Scheme.Modules.derivedPullback g).obj
        ((Scheme.Modules.derivedPushforward f).obj
          ((DerivedCategory.singleFunctor.{u} X.Modules 0).obj G)) ≅
      (Scheme.Modules.derivedPushforward (pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor.{u} (pullback f g).Modules 0).obj
          ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))) := by
  let : ∀ Y : Scheme.{u},
      HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    fun Y ↦ HasDerivedCategory.ofIsGrothendieckAbelian _
  let F := Scheme.Modules.tensorPullback (pullback.fst f g)
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction (pullback.fst f g)
  let : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : F.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ F
    (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  obtain ⟨c, _, hc⟩ := exists_isIso_canonicalModuleBaseChange_of_isFlatOver
    f g (pullback.fst f g) (pullback.snd f g) (IsPullback.of_hasPullback f g) G hflat
  have := hc
  let a := asIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
        (schemeDerivedDirectImage (pullback.snd f g)).map c)
  obtain ⟨s⟩ := sourceModelIso f G g
  obtain ⟨t⟩ := targetModelIso f G g
  exact ⟨s.symm ≪≫ (schemeDerivedCategoryEquiv T).functor.mapIso a ≪≫ t⟩

/-- Derived pullback of the derived direct image of a quasi-coherent module flat over
its base is isomorphic to the derived direct image of its ordinary tensor pullback.
Source: Weil conjectures blueprint, sec-picard-framework/sk-thm-picard-semicon,
lemma lem-pc-rf-base-change-flat-module (blueprint: lem-pc-rf-base-change-flat-module).

Proof:
1. Use `exists_isIso_canonicalModuleBaseChange_of_isFlatOver`, whose finite affine
   Cech proof computes derived pullback using the flat terms and identifies the
   tensor complex with the Cech complex after base change. It proves invertibility
   of the canonical map to the ordinary pulled-back module.
2. Compare the chosen derived categories with the fixed model
   `DerivedCategory X.Modules`. Single objects agree by compatibility with Q;
   direct images agree because the same K-injective resolution computes both;
   derived pullback agrees by `derivedPullback_def`.
3. Apply the canonical theorem with the Grothendieck derived-category instances
   in universe u for all schemes, then transport its isomorphism to the fixed
   model using these comparisons.
4. For the four given instances in arbitrary universe w, compare the source and
   target with this same fixed model. Compose the isomorphisms and reflect back
   through the fully faithful comparison equivalence. This preserves the four
   original instance hypotheses; no global choice in universe w is assumed. -/
theorem nonempty_derivedBaseChange_iso_of_isFlatOver
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    (G : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [SheafOfModules.IsQuasicoherent.{u} (R := moduleRings X.toRingedSpace) G]
    (hflat : Scheme.Modules.IsFlatOver G f)
    (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))] :
    Nonempty
      ((derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)) ≅
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))) := by
  obtain ⟨s⟩ := sourceModelIso f G g
  obtain ⟨t⟩ := targetModelIso f G g
  obtain ⟨a⟩ := moduleModelBaseChange f G hflat g
  exact ⟨(schemeDerivedCategoryEquiv T).functor.preimageIso (s ≪≫ a ≪≫ t.symm)⟩

end

end AlgebraicGeometry
