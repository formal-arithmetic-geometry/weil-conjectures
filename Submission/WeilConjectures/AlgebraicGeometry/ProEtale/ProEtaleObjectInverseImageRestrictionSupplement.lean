/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Pullback
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Inverse image along an object of the small pro-etale site

Source: Stacks Project, Sites and Sheaves, Tags 03CE, 00VC, 00XZ, 00WH and 0H7J;
Modules on Sites, Tags 03D2 and 03EK; pro-etale functoriality, Tag 09A5
(blueprint: lem-sfb-proetale-object-inverse-image-restriction).

The comparison data below spell out the canonical presheaf coprojections and
sheafification unit. The theorem applies to an arbitrary site object, with no
monomorphism or finiteness hypothesis.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def restrictionPresheafIso {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D] :
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ⋙
        sheafToPresheaf (ProEt.topology W.left) D ≅
      sheafToPresheaf (ProEt.topology X) D ⋙ (proEtaleBaseChange W.hom).op.lan := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom
    W.prop trivial).op.whiskerLeft D
  let b := (proEtaleBaseChange W.hom).op.lanAdjunction D
  exact Functor.isoWhiskerLeft (sheafToPresheaf (ProEt.topology X) D)
    (a.leftAdjointUniq b)

private theorem restrictionPresheafIso_coprojection {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : Sheaf (ProEt.topology X) D) (U : W.left.ProEt) :
    ((restrictionPresheafIso W D).hom.app G).app (op U) =
      ((proEtaleBaseChange W.hom).op.leftKanExtensionUnit G.obj).app
          (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) ≫
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj).map
          (proEtaleObjectInverseImageIndexPoint W U).hom.op := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    W.hom W.prop trivial).op.whiskerLeft D
  let b := (proEtaleBaseChange W.hom).op.lanAdjunction D
  have h : (a.leftAdjointUniq b).hom.app G.obj =
      (a.homEquiv _ _).symm (b.unit.app G.obj) := by
    apply (a.homEquiv _ _).injective
    exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a b G.obj).trans
      (Equiv.apply_symm_apply _ _).symm
  change ((a.leftAdjointUniq b).hom.app G.obj).app (op U) = _
  rw [h, Adjunction.homEquiv_counit]
  simp only [a, b, NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, Adjunction.whiskerLeft_counit_app_app,
    Functor.lanAdjunction_unit]
  rfl

private theorem restrictionLan_isSheaf {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : Sheaf (ProEt.topology X) D) :
    Presheaf.IsSheaf (ProEt.topology W.left)
      (((proEtaleBaseChange W.hom).op.lan).obj G.obj) :=
  (Presheaf.isSheaf_of_iso_iff ((restrictionPresheafIso W D).app G)).mp
    ((AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop).obj G).property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def restrictionComparison {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology W.left) D] :
    ProEtaleObjectRestrictionComparison W D := by
  let p := restrictionPresheafIso W D
  have hq (G : Sheaf (ProEt.topology X) D) :
      IsIso (toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)) :=
    isIso_toSheafify _ (restrictionLan_isSheaf W D G)
  let e : AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ≅
      proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D :=
    NatIso.ofComponents (fun G ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (p.app G ≪≫ asIso (toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)))) (by
      intro G H f
      apply Sheaf.hom_ext
      change _ ≫ (p.hom.app H ≫ toSheafify _ _) =
        (p.hom.app G ≫ toSheafify _ _) ≫ _
      have hp := p.hom.naturality f
      change ((AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop).map
        f).hom ≫ p.hom.app H = p.hom.app G ≫
          ((proEtaleBaseChange W.hom).op.lan).map f.hom at hp
      rw [← Category.assoc, hp, Category.assoc]
      have hfmap :
          ((proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D).map f).hom =
          sheafifyMap (ProEt.topology W.left)
            (((proEtaleBaseChange W.hom).op.lan).map f.hom) := by
        rfl
      rw [hfmap]
      rw [Category.assoc]
      congr 1
      exact toSheafify_naturality (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).map f.hom))
  exact
    { presheafIso := p
      coprojection := restrictionPresheafIso_coprojection W D
      sheafification_isIso := hq
      sheafIso := e.symm
      sheafIso_inv := fun _ ↦ rfl }

end AlgebraicGeometry.Scheme
