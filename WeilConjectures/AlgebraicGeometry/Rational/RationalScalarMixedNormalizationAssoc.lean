/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Rational.RationalScalarBalancedLocalization
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle

/-! # Associativity of the specified derived scalar normalizations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  proEtaleRingInverseImageComp LocallyRingedSpace.comp PresheafedSpace.comp

private theorem mixed_normalization_mate {W : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : R ⟶ T) (h : a ≫ b = c)
    (K : DerivedCategory (pbcModules W R)) :
    (pbcReductionNormalization a b c h K).hom =
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction c)
        (pbcDerivedRestrictComp a b c h)).hom.app K := by
  dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]

/-- The specified derived scalar normalizations satisfy the associativity equation.
Source: BS Remark 6.8.15; Stacks 0D6D, 07A4.
(blueprint: lem-per-mixed-reduction-normalization-assoc).

Proof: the underlying restriction comparisons are the identity on sections, so
their cocycle holds sectionwise. The derived comparison cocycle transports this
equation to derived restriction. Mathlib's associativity of left-adjoint
composition comparisons then proves the equation, because the prescribed
normalization is precisely the adjunction mate of each restriction comparison. -/
theorem rationalMixedReductionNormalizationAssoc {W : Scheme.{u}}
    {R S T V : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V)
    (ab : R ⟶ T) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc)
    (K : DerivedCategory (pbcModules W R)) :
    (pbcDerivedExtend c).map ((pbcReductionNormalization a b ab hab K).hom) ≫
        (pbcReductionNormalization ab c abc hl K).hom =
      (pbcReductionNormalization b c bc hbc ((pbcDerivedExtend a).obj K)).hom ≫
        (pbcReductionNormalization a bc abc hr K).hom := by
  have ho (M : pbcModules W V) :
      (pbcRestrict a).map ((pbcRestrictComp b c bc hbc).hom.app M) ≫
          (pbcRestrictComp a bc abc hr).hom.app M =
        (pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M) ≫
          (pbcRestrictComp ab c abc hl).hom.app M := by
    ext U x
    change ((pbcRestrictComp a bc abc hr).hom.app M).val.app U
        (((pbcRestrictComp b c bc hbc).hom.app M).val.app U x) =
      ((pbcRestrictComp ab c abc hl).hom.app M).val.app U
        (((pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M)).val.app U x)
    simp only [pbcRestrictComp, (pbcRestrictComp_exists a bc abc hr).exists.choose_spec,
      (pbcRestrictComp_exists b c bc hbc).exists.choose_spec,
      (pbcRestrictComp_exists ab c abc hl).exists.choose_spec,
      (pbcRestrictComp_exists a b ab hab).exists.choose_spec]
  have hd (M : DerivedCategory (pbcModules W V)) :=
    Functor.mapDerivedCategoryCompNatIso_cocycle
      (pbcRestrictComp b c bc hbc) (pbcRestrictComp a bc abc hr)
      (pbcRestrictComp a b ab hab) (pbcRestrictComp ab c abc hl) ho M
  have hrest :
      Functor.isoWhiskerLeft (pbcDerivedRestrict c) (pbcDerivedRestrictComp a b ab hab) ≪≫
          pbcDerivedRestrictComp ab c abc hl =
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (pbcDerivedRestrictComp b c bc hbc) (pbcDerivedRestrict a) ≪≫
            pbcDerivedRestrictComp a bc abc hr := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp, pbcDerivedRestrictComp,
      pbcDerivedRestrict, Functor.mapDerivedCategoryCompNatIso] using (hd M).symm
  have he := Adjunction.leftAdjointCompIso_assoc
    (pbcDerivedScalarAdjunction a) (pbcDerivedScalarAdjunction b)
    (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction ab)
    (pbcDerivedScalarAdjunction bc) (pbcDerivedScalarAdjunction abc)
    (pbcDerivedRestrictComp a b ab hab) (pbcDerivedRestrictComp b c bc hbc)
    (pbcDerivedRestrictComp a bc abc hr) (pbcDerivedRestrictComp ab c abc hl) hrest
  have heK := congrArg (fun e ↦ e.hom.app K) he
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at heK
  simpa only [mixed_normalization_mate] using heK.symm


end AlgebraicGeometry.Scheme
