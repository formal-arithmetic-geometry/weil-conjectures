/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingRestrictionSquare
import WeilConjectures.AlgebraicGeometry.StrictTowerRingedSquare.ProEtaleRingedSquareLocalization
import all WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSquare
public import WeilConjectures.CategoryTheory.ExactCube
public import WeilConjectures.CategoryTheory.MateCube
/-! Finite coefficient reduction and the canonical inverse-image square.
Source: Stacks Project, Tags 0D6D and 0E48.
(blueprint: lem-weil-pbc-finite-reduction-pullback-square) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
attribute [local instance 2000] proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] completedAdicDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor proEtaleRingModulePullback
  proEtaleRingModuleAdjunction proEtaleRingDerivedAdjunction
  proEtaleAmbientRingedPullbackComparison
section Generic

private theorem invert_compositor {C : Type*} [Category C]
    {A B D E : C} (c : A ≅ B) (d : D ≅ E) (u : A ⟶ D) (v : B ⟶ E)
    (h : c.hom ≫ v = u ≫ d.hom) : c.inv ≫ u = v ≫ d.inv := by
  apply (cancel_epi c.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private def ordinaryRestrictionIso {U V : Scheme.{t}} (u : U ⟶ V)
    (RV SV : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
    (RU SU : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
    (aV : RV ⟶ SV) (aU : RU ⟶ SU)
    (cR : (proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj RV ≅ RU)
    (cS : (proEtaleSheafInverseImage u CommRingCat.{t + 1}).obj SV ≅ SU)
    (h : cR.hom ≫ aU = (proEtaleSheafInverseImage u CommRingCat.{t + 1}).map aV ≫ cS.hom) :
    proEtaleRingRestrictScalars aV ⋙ proEtaleRingModulePullback u RV RU cR ≅
      proEtaleRingModulePullback u SV SU cS ⋙ proEtaleRingRestrictScalars aU :=
  @asIso _ _ _ _ (proEtaleRingRestrictionPullbackInv u RV SV RU SU aV aU cR cS h)
    (proEtaleRingRestrictionPullbackInv_isIso u RV SV RU SU aV aU cR cS h)

private theorem genericReductionSquare (M : DerivedCategory (proEtaleRingModules Y r.RY)) :
    (proEtaleRingDerivedPullback f' s.RY' s.RX' s.cf').map
      ((proEtaleReductionPullbackIso g r.RY s.RY r.RY' s.RY' aY aY' r.cg s.cg hg).hom.app M) ≫
      (proEtaleReductionPullbackIso f' r.RY' s.RY' r.RX' s.RX' aY' aX' r.cf' s.cf' hf').hom.app
        ((proEtaleRingDerivedPullback g r.RY r.RY' r.cg).obj M) ≫
      (proEtaleRingDerivedExtension aX').map
        ((proEtaleAmbientRingedPullbackComparison sq
          r.RX r.RY r.RX' r.RY'
          r.cf r.cg r.cg' r.cf' r.coherent).hom.app M) =
    (proEtaleAmbientRingedPullbackComparison sq
        s.RX s.RY s.RX' s.RY'
        s.cf s.cg s.cg' s.cf' s.coherent).hom.app ((proEtaleRingDerivedExtension aY).obj M) ≫
      (proEtaleRingDerivedPullback g' s.RX s.RX' s.cg').map
      ((proEtaleReductionPullbackIso f r.RY s.RY r.RX s.RX aY aX r.cf s.cf hf).hom.app M) ≫
      (proEtaleReductionPullbackIso g' r.RX s.RX r.RX' s.RX' aX aX' r.cg' s.cg' hg').hom.app
        ((proEtaleRingDerivedPullback f r.RY r.RX r.cf).obj M) := by
  let qf := ordinaryRestrictionIso f r.RY s.RY r.RX s.RX aY aX r.cf s.cf hf
  let qg := ordinaryRestrictionIso g r.RY s.RY r.RY' s.RY' aY aY' r.cg s.cg hg
  let qg' := ordinaryRestrictionIso g' r.RX s.RX r.RX' s.RX' aX aX' r.cg' s.cg' hg'
  let qf' := ordinaryRestrictionIso f' r.RY' s.RY' r.RX' s.RX' aY' aX' r.cf' s.cf' hf'
  have ho (N : proEtaleRingModules Y s.RY) :
      r.exchangeModuleSquare.inv.app ((proEtaleRingRestrictScalars aY).obj N) ≫
        (proEtaleRingModulePullback f' r.RY' r.RX' r.cf').map (qg.hom.app N) ≫
          qf'.hom.app ((proEtaleRingModulePullback g s.RY s.RY' s.cg).obj N) =
      (proEtaleRingModulePullback g' r.RX r.RX' r.cg').map (qf.hom.app N) ≫
        qg'.hom.app ((proEtaleRingModulePullback f s.RY s.RX s.cf).obj N) ≫
          (proEtaleRingRestrictScalars aX').map (s.exchangeModuleSquare.inv.app N) := by
    have h := proEtaleRingRestriction_square r s aY aX aY' aX' hf hg hg' hf' N
    have h' := invert_compositor
      (r.exchangeModuleSquare.app ((proEtaleRingRestrictScalars aY).obj N))
      ((proEtaleRingRestrictScalars aX').mapIso (s.exchangeModuleSquare.app N))
      ((proEtaleRingModulePullback f' r.RY' r.RX' r.cf').map (qg.hom.app N) ≫
        qf'.hom.app ((proEtaleRingModulePullback g s.RY s.RY' s.cg).obj N))
      ((proEtaleRingModulePullback g' r.RX r.RX' r.cg').map (qf.hom.app N) ≫
        qg'.hom.app ((proEtaleRingModulePullback f s.RY s.RX s.cf).obj N))
      (by simpa only [qf, qg, qf', qg', ordinaryRestrictionIso, asIso_hom,
        Iso.app_hom, Functor.mapIso_hom, Category.assoc] using h)
    simpa only [Iso.app_inv, Functor.mapIso_inv, Category.assoc] using h'
  have hd := CategoryTheory.Functor.exactDerivedCube
    (R₀ := proEtaleRingRestrictScalars aY) (R₁ := proEtaleRingRestrictScalars aX)
    (R₂ := proEtaleRingRestrictScalars aY') (R₃ := proEtaleRingRestrictScalars aX')
    (J := proEtaleRingModulePullback f r.RY r.RX r.cf)
    (H := proEtaleRingModulePullback g' r.RX r.RX' r.cg')
    (G := proEtaleRingModulePullback g r.RY r.RY' r.cg)
    (I := proEtaleRingModulePullback f' r.RY' r.RX' r.cf')
    (J' := proEtaleRingModulePullback f s.RY s.RX s.cf)
    (H' := proEtaleRingModulePullback g' s.RX s.RX' s.cg')
    (G' := proEtaleRingModulePullback g s.RY s.RY' s.cg)
    (I' := proEtaleRingModulePullback f' s.RY' s.RX' s.cf')
    qf qg' qg qf' r.exchangeModuleSquare.symm s.exchangeModuleSquare.symm ho
  have hm := CategoryTheory.scalarMateCube
    (J := proEtaleRingDerivedPullback f r.RY r.RX r.cf)
    (H := proEtaleRingDerivedPullback g' r.RX r.RX' r.cg')
    (G := proEtaleRingDerivedPullback g r.RY r.RY' r.cg)
    (I := proEtaleRingDerivedPullback f' r.RY' r.RX' r.cf')
    (J' := proEtaleRingDerivedPullback f s.RY s.RX s.cf)
    (H' := proEtaleRingDerivedPullback g' s.RX s.RX' s.cg')
    (G' := proEtaleRingDerivedPullback g s.RY s.RY' s.cg)
    (I' := proEtaleRingDerivedPullback f' s.RY' s.RX' s.cf')
    (proEtaleRingDerivedExtensionAdjunction aY) (proEtaleRingDerivedExtensionAdjunction aX)
    (proEtaleRingDerivedExtensionAdjunction aY') (proEtaleRingDerivedExtensionAdjunction aX')
    (Functor.mapDerivedCategorySquareIso qf).hom
    (Functor.mapDerivedCategorySquareIso qg').hom
    (Functor.mapDerivedCategorySquareIso qg).hom
    (Functor.mapDerivedCategorySquareIso qf').hom
    (Functor.mapDerivedCategorySquareIso r.exchangeModuleSquare.symm).hom
    (Functor.mapDerivedCategorySquareIso s.exchangeModuleSquare.symm).hom hd M
  let θr := proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
    r.cf r.cg r.cg' r.cf' r.coherent
  let θs := proEtaleAmbientRingedPullbackComparison sq s.RX s.RY s.RX' s.RY'
    s.cf s.cg s.cg' s.cf' s.coherent
  have hr : (Functor.mapDerivedCategorySquareIso r.exchangeModuleSquare.symm).hom =
      θr.inv := by
    dsimp only [θr]
    rw [r.ambientSquare_localization]
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  have hs : (Functor.mapDerivedCategorySquareIso s.exchangeModuleSquare.symm).hom =
      θs.inv := by
    dsimp only [θs]
    rw [s.ambientSquare_localization]
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hr, hs] at hm
  let χf := proEtaleReductionPullbackIso f r.RY s.RY r.RX s.RX aY aX r.cf s.cf hf
  let χg := proEtaleReductionPullbackIso g r.RY s.RY r.RY' s.RY' aY aY' r.cg s.cg hg
  let χg' := proEtaleReductionPullbackIso g' r.RX s.RX r.RX' s.RX' aX aX' r.cg' s.cg' hg'
  let χf' := proEtaleReductionPullbackIso f' r.RY' s.RY' r.RX' s.RX' aY' aX' r.cf' s.cf' hf'
  let L := (proEtaleRingDerivedPullback f' s.RY' s.RX' s.cf').mapIso (χg.app M) ≪≫
    χf'.app ((proEtaleRingDerivedPullback g r.RY r.RY' r.cg).obj M) ≪≫
    (proEtaleRingDerivedExtension aX').mapIso (θr.app M)
  let Q := θs.app ((proEtaleRingDerivedExtension aY).obj M) ≪≫
    (proEtaleRingDerivedPullback g' s.RX s.RX' s.cg').mapIso (χf.app M) ≪≫
    χg'.app ((proEtaleRingDerivedPullback f r.RY r.RX r.cf).obj M)
  apply (Iso.inv_eq_inv L Q).mp
  simpa only [L, Q, χf, χg, χf', χg', proEtaleReductionPullbackIso,
    proEtaleReductionPullbackInv, proEtaleRingRestrictionDerivedPullback,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, ← Functor.mapDerivedCategoryNatIso_symm,
    Iso.symm_symm_eq, Category.assoc, asIso_hom, qf, qg, qf', qg', ordinaryRestrictionIso,
    Iso.app_inv, Functor.mapIso_inv] using hm

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
variable (r s : StrictTowerRingedSquare sq)
  (aY : r.RY ⟶ s.RY) (aX : r.RX ⟶ s.RX)
  (aY' : r.RY' ⟶ s.RY') (aX' : r.RX' ⟶ s.RX')
  (hf : r.cf.hom ≫ aX =
    (proEtaleSheafInverseImage f CommRingCat.{t + 1}).map aY ≫ s.cf.hom)
  (hg : r.cg.hom ≫ aY' =
    (proEtaleSheafInverseImage g CommRingCat.{t + 1}).map aY ≫ s.cg.hom)
  (hg' : r.cg'.hom ≫ aX' =
    (proEtaleSheafInverseImage g' CommRingCat.{t + 1}).map aX ≫ s.cg'.hom)
  (hf' : r.cf'.hom ≫ aX' =
    (proEtaleSheafInverseImage f' CommRingCat.{t + 1}).map aY' ≫ s.cf'.hom)

end Generic

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

end AlgebraicGeometry.Scheme
