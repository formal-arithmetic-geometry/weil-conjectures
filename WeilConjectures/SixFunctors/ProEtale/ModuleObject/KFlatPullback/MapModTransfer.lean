/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.KFlatPullback.UpperStarFull

/-!
# K-flatness of `mapMod(f^*)` from K-flatness of the pullback

The pullback `f^* = mapMod(f^*) ⋙ Ext_{α_f}` of module objects over `Λ` differs from
`mapMod(f^*) : Mod_{Λ_Y} ⥤ Mod_{f^* Λ_Y}` by the monoidal equivalence `Ext_{α_f}`, so a complex
`mapMod(f^*) K` is K-flat as soon as `f^* K` is
(`AlgebraicGeometry.ProEtale.CondensedRing.kFlat_mapMod_upperStar_of_kFlat_upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Restriction of scalars along `α_f` undoes the extension of scalars in `f^*`. -/
noncomputable def upperStarCompComapIso :
    (f)^*⟦Λ⟧ ⋙ Mod.comap (condensedPullbackHom Λ f) ≅
      (f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)) _ ≪≫
      (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).counitIso) ≪≫
    Functor.rightUnitor _

/-- If the pullback `f^* K` of a complex of module objects over `Λ_Y` is K-flat, so is
`mapMod(f^*) K`. -/
lemma kFlat_mapMod_upperStar_of_kFlat_upperStar
    (K : CochainComplex (Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ)
    (hK : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (((f)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ)
      |>.obj K)) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).mapHomologicalComplex (.up ℤ)).obj K) :=
  have : (Mod.comap (condensedPullbackHom Λ f) :
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
        Mod _ ((f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y))).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).isEquivalence_functor
  ObjectProperty.prop_of_iso _
    ((Functor.mapHomologicalComplexCompIso (upperStarCompComapIso Λ f) (.up ℤ)).app K)
    ((Mod.comap (condensedPullbackHom Λ f)).kFlat_mapHomologicalComplex_obj_of_isEquivalence hK)

end AlgebraicGeometry.ProEtale.CondensedRing
