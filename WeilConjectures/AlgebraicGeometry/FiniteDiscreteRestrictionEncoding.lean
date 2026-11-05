/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientEncodingData
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientSections
/-! # Restriction compatibility of the fixed coefficient encoding -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

private local instance restrictionEncodingEssentiallySmall :
    EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

local instance finiteDiscreteRestrictionEncodingInst1 (T : AlgebraicGeometry.Scheme.{u}) :
    ((AlgebraicGeometry.Scheme.ProEt.topology T).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal (J := AlgebraicGeometry.Scheme.ProEt.topology T)
    (A := Ab.{u + 1})

local instance finiteDiscreteRestrictionEncodingInst2 (T : AlgebraicGeometry.Scheme.{u}) :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1} :=
  HasSheafify.isRightAdjoint

noncomputable local instance (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.monoidalCategory (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

open CategoryTheory.ConstantInternalModuleSheafEncoding MonoidalCategory

set_option hygiene false in
local notation "ΛB" => Profinite.continuousMapRingObj B

private noncomputable def coefficientUnit (T : Scheme.{u}) :
    A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B) ⟶
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T).obj :=
  (sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
      (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)) ≫
    (finiteDiscreteSchemeRingIso B T eR).hom.hom

private lemma encoding_action (T : Scheme.{u})
    (M : FiniteDiscreteInternalModules B T) (V : T.ProEtᵒᵖ) :
    Mod.act (A := AddCommGrpCat.of (ULift.{u + 1} B))
      (((presheafToFunctor (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)).obj
        ((moduleLocalizationRight (ProEt.topology T)
          (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))).obj
          ((Mod.comap (finiteDiscreteSchemeRingIso B T eR).hom).obj M))).obj V).X =
    (coefficientUnit B eR T).app V ▷ M.X.obj.obj V ≫
      (Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T) M.X).app V ≫
      (Mod.act (A := condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
        M.X).hom.app V := by
  dsimp only [presheafToFunctor, moduleLocalizationRight, Adjunction.modRight,
    Functor.comp_obj]
  simp only [Functor.act_mapMod_obj, Mod.act_comap_obj]
  dsimp only [CategoryTheory.evaluation_obj_map, CategoryTheory.evaluation_obj_obj]
  change (((sheafificationAdjunction (ProEt.topology T) Ab.{u + 1}).unit.app
      (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B)) ▷ M.X.obj ≫
    Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T) Ab.{u + 1})
      ((presheafToSheaf (ProEt.topology T) Ab.{u + 1}).obj
        (A (C := T.ProEtᵒᵖ) (ULift.{u + 1} B))) M.X ≫
    (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}).map
      ((finiteDiscreteSchemeRingIso B T eR).hom ▷ M.X) ≫
    (sheafToPresheaf (ProEt.topology T) Ab.{u + 1}).map
      (Mod.act (A := condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)
        M.X)).app V) = _
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  simp only [NatTrans.comp_app, Monoidal.whiskerRight_app,
    coefficientUnit, Category.assoc, comp_whiskerRight]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

section

open CategoryTheory Limits
open scoped CategoryTheory.Obj
open Scheme
variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))
set_option hygiene false in
local notation "ΛB" => Profinite.continuousMapRingObj B

open CategoryTheory.ConstantInternalModuleSheafEncoding MonoidalCategory

end

end AlgebraicGeometry.ProEtale.CondensedRing
