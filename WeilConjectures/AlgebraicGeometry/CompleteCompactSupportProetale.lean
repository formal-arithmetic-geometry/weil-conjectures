/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.AlgebraicGeometry.ProjectionCompactification
public import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import all WeilConjectures.AlgebraicGeometry.CompleteProetale
public import WeilConjectures.AlgebraicGeometry.CompletedExchangeCoherence
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.Compactification.Cofiltered
import WeilConjectures.AlgebraicGeometry.OrdinaryOpenExchangeIdentity
import WeilConjectures.AlgebraicGeometry.CompletedPullbackReflection

import all WeilConjectures.AlgebraicGeometry.OpenImmersionTensorPiece
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ClopenScalarRestrictionReverseAdjunction
import WeilConjectures.CategoryTheory.ExactDerivedAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.StrictTowerExchangeMateNormalization
import WeilConjectures.AlgebraicGeometry.RingedOpenStrictReduction
import WeilConjectures.AlgebraicGeometry.CompletedOpenFiniteEtaleOrigins
import WeilConjectures.AlgebraicGeometry.CompletedKoszulQuotientComparison
import all WeilConjectures.AlgebraicGeometry.CompletedFiniteExchangeCoordinates

/-!
# Complete pro-etale compact-support base change

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-cbc,
node thm-cbc-complete-proetale (blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The projection of an open pullback, as an arrow in the original pro-etale site.
Source: Stacks 09AE, localization (blueprint: thm-cbc-complete-proetale). -/
def cbcOpenProjection {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (V : T.ProEt) :
    (cbcOpenSiteFunctor j inferInstance).obj ((proEtaleBaseChange j).obj V) ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom j) pullback.condition

/-- The coefficient counit equation follows from the constant-sheafification unit. -/
private theorem cbcFiniteCoefficientCounit {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] (n : ℕ) :
    let F := proEtaleBaseChange j
    let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial
    let R := ProEtale.StrictTower.coefficients (cbcFiniteRing d n) T
    let S := ProEtale.StrictTower.coefficients (cbcFiniteRing d n) U
    let ψ := proEtaleRingDirectImageMap j R S
      (ProEtale.StrictTower.constantRingIso (cbcFiniteRing d n) j)
    Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ F.op.whiskerLeft (finiteOpenRing d j inferInstance n).hom.hom := by
  dsimp only
  let F := proEtaleBaseChange j
  let G := cbcOpenSiteFunctor j inferInstance
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let R := ProEtale.StrictTower.coefficients (cbcFiniteRing d n) T
  let S := ProEtale.StrictTower.coefficients (cbcFiniteRing d n) U
  let ψ := proEtaleRingDirectImageMap j R S
    (ProEtale.StrictTower.constantRingIso (cbcFiniteRing d n) j)
  have hψ : ψ = proEtaleConstantDirectImageMap j CommRingCat.{t + 1}
      (cbcFiniteRing d n) := by
    change (proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv _ _
      (((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv _ _).symm _) = _
    exact Equiv.apply_symm_apply _ _
  change Functor.whiskerRight (NatTrans.op a.counit) R.obj =
    ψ.hom ≫ F.op.whiskerLeft (finiteOpenRing d j inferInstance n).hom.hom
  apply sheafify_hom_ext (ProEt.topology T) _ _
    (((proEtaleSheafDirectImage j CommRingCat.{t + 1}).obj
      ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj R)).property)
  rw [hψ]
  have hunit : toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n)) ≫
      (proEtaleConstantDirectImageMap j CommRingCat.{t + 1}
        (cbcFiniteRing d n)).hom =
      F.op.whiskerLeft (toSheafify (ProEt.topology U)
        ((Functor.const U.ProEtᵒᵖ).obj (cbcFiniteRing d n))) := by
    exact (sheafificationAdjunction (ProEt.topology T) CommRingCat.{t + 1}).homEquiv
      _ _ |>.apply_symm_apply _
  rw [← Category.assoc]
  erw [hunit]
  ext V b
  have hc := ConcreteCategory.congr_hom
    (congr_app (finiteOpenRing_unit d j inferInstance n) (F.op.obj V)) b
  have hn := ConcreteCategory.congr_hom
    ((toSheafify (ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (cbcFiniteRing d n))).naturality
        (a.counit.app V.unop).op) b
  exact hn.symm.trans hc.symm

/-- Completed scalar compatibility is detected by the finite limit projections. -/
private theorem cbcCompletedCoefficientCounit {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    let F := proEtaleBaseChange j
    let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
      (inferInstance : WeaklyEtale j) trivial
    let ψ := proEtaleRingDirectImageMap j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)
    Functor.whiskerRight (NatTrans.op a.counit) (d.completedRing T).obj =
      ψ.hom ≫ F.op.whiskerLeft (cbcCompletedRestrictionMap d j inferInstance).hom := by
  let F := proEtaleBaseChange j
  let G := cbcOpenSiteFunctor j inferInstance
  let E := sheafToPresheaf (ProEt.topology T) CommRingCat.{t + 1} ⋙
    (Functor.whiskeringLeft T.ProEtᵒᵖ T.ProEtᵒᵖ CommRingCat.{t + 1}).obj (F ⋙ G).op
  apply (isLimitOfPreserves E (limit.isLimit (reductionCoefficientSystem T d))).hom_ext
  intro n
  dsimp only [Functor.mapCone_π_app, Functor.comp_map]
  apply (cancel_mono (E.map (pbcLevelConstantComparison T d n.unop).inv)).1
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let π := cbcFiniteProjection d T n.unop
  let π' := cbcFiniteProjection d U n.unop
  let ψ := cbcCompletedCoefficientDirectMap d j
  let ψ' := proEtaleRingDirectImageMap j
    (ProEtale.StrictTower.coefficients (cbcFiniteRing d n.unop) T)
    (ProEtale.StrictTower.coefficients (cbcFiniteRing d n.unop) U)
    (ProEtale.StrictTower.constantRingIso (cbcFiniteRing d n.unop) j)
  have hψ : proEtaleRingDirectImageMap j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j) = ψ := by
    dsimp [ψ, cbcCompletedCoefficientDirectMap, proEtaleRingDirectImageMap]
    rw [cbcDatumCoefficient_eq d j]
    rfl
  have hπ : ψ.hom ≫ F.op.whiskerLeft π'.hom = π.hom ≫ ψ'.hom := by
    exact congrArg (fun z ↦ z.hom) (finiteProjection_direct d j n.unop).symm
  have hres : (cbcCompletedRestrictionMap d j inferInstance).hom ≫
      G.op.whiskerLeft π.hom = π'.hom ≫ (finiteOpenRing d j inferInstance n.unop).hom.hom := by
    exact congrArg (fun z ↦ z.hom) (finiteOpenRing_projection d j inferInstance n.unop).symm
  change Functor.whiskerRight (NatTrans.op a.counit) (d.completedRing T).obj ≫
      (F ⋙ G).op.whiskerLeft π.hom =
    (proEtaleRingDirectImageMap j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).hom ≫
      F.op.whiskerLeft (cbcCompletedRestrictionMap d j inferInstance).hom ≫
        (F ⋙ G).op.whiskerLeft π.hom
  rw [hψ]
  have hn : Functor.whiskerRight (NatTrans.op a.counit) (d.completedRing T).obj ≫
      (F ⋙ G).op.whiskerLeft π.hom =
    π.hom ≫ Functor.whiskerRight (NatTrans.op a.counit)
      (ProEtale.StrictTower.coefficients (cbcFiniteRing d n.unop) T).obj := by
    apply NatTrans.ext
    funext V
    exact π.hom.naturality (a.counit.app V.unop).op
  rw [hn, cbcFiniteCoefficientCounit d j n.unop]
  calc
    _ = (π.hom ≫ ψ'.hom) ≫
        F.op.whiskerLeft (finiteOpenRing d j inferInstance n.unop).hom.hom := by
      rfl
    _ = (ψ.hom ≫ F.op.whiskerLeft π'.hom) ≫
        F.op.whiskerLeft (finiteOpenRing d j inferInstance n.unop).hom.hom := by rw [hπ]
    _ = ψ.hom ≫ F.op.whiskerLeft
        (π'.hom ≫ (finiteOpenRing d j inferInstance n.unop).hom.hom) := by
      rfl
    _ = _ := by rw [← hres]; rfl

/-- Lift the open-site adjunction using the normalized coefficient counit equation. -/
private def cbcRestrictionAdjunction {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    cbcOpenRestriction d j inferInstance ⊣
      proEtaleRingModuleDirectImage j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j) := by
  let F := proEtaleBaseChange j
  let G := cbcOpenSiteFunctor j inferInstance
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let R := d.completedRing T
  let S := d.completedRing U
  let c := cbcCompletedRestrictionMap d j inferInstance
  let ψ := proEtaleRingDirectImageMap j R S (d.integralRingIso j)
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ F.op.whiskerLeft c.hom := cbcCompletedCoefficientCounit d j
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{t + 1})
    (ProEt.topology U) (ProEt.topology T)
  let e := ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).leftAdjointUniq b).app R
  have hc : (d.integralRingIso j).hom ≫ c = e.hom := by
    apply ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv _ _).injective
    change ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv R
      ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj R)) ((d.integralRingIso j).hom ≫ c) =
      ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv R
        ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj R))
        (((proEtaleSheafAdjunction j CommRingCat.{t + 1}).leftAdjointUniq b).hom.app R)
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    apply Sheaf.hom_ext
    change ψ.hom ≫ F.op.whiskerLeft c.hom =
      Functor.whiskerRight (NatTrans.op a.counit) R.obj
    exact H₁.symm
  have heq : c = ((d.integralRingIso j).symm ≪≫ e).hom := by
    apply (cancel_epi (d.integralRingIso j).hom).1
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc] using hc
  have : IsIso c := by rw [heq]; infer_instance
  have H₂ : c.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (c.hom.app V)).1
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun z ↦ z.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (c.hom.app (F.op.obj (G.op.obj V)))
      (R.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.app V ≫ R.obj.map (𝟙 (G.op.obj V)) = c.hom.app V
    rw [R.obj.map_id]
    exact Category.comp_id _
  let Rr := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let Sr := (sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj S
  let φr : Sr ⟶ (G.sheafPushforwardContinuous RingCat.{t + 1}
      (ProEt.topology U) (ProEt.topology T)).obj Rr :=
    (sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map c
  let ψr : Rr ⟶ (F.sheafPushforwardContinuous RingCat.{t + 1}
      (ProEt.topology T) (ProEt.topology U)).obj Sr :=
    ⟨Functor.whiskerRight ψ.hom (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})⟩
  have H₁r : Functor.whiskerRight (NatTrans.op a.counit) Rr.obj =
      ψr.hom ≫ F.op.whiskerLeft φr.hom := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}).map
      (z.app V)) H₁
  have H₂r : φr.hom ≫ G.op.whiskerLeft ψr.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) Sr.obj = 𝟙 Sr.obj := by
    apply NatTrans.ext
    funext V
    exact congrArg (fun z ↦ (forget₂ CommRingCat.{t + 1} RingCat.{t + 1}).map
      (z.app V)) H₂
  exact SheafOfModules.pushforwardPushforwardAdj a φr ψr H₁r H₂r

private theorem cbcRestrictionAdjunction_unit {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] (M : proEtaleRingModules T (d.completedRing T)) (V : T.ProEt)
    (x : M.val.obj (op V)) :
    ((cbcRestrictionAdjunction d j).unit.app M).val.app (op V) x =
      M.val.map (cbcOpenProjection j V).op x := by
  unfold cbcRestrictionAdjunction
  rfl

/-- Restriction of sections is the unit from a module to direct image of open restriction.
Its section formula fixes the comparison, including its completed scalar action.
Source: Stacks 03DI and 09AE (blueprint: thm-cbc-complete-proetale).
Proof: apply each presheaf restriction to the displayed pullback projection. Functoriality
makes these maps natural. The finite coefficient projections show scalar compatibility;
limit uniqueness gives the same compatibility for completed coefficients. The formula on
all sections uniquely determines a sheaf map and then the natural transformation. -/
theorem cbcRestrictionUnit_existsUnique {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    ∃! η : 𝟭 (proEtaleRingModules T (d.completedRing T)) ⟶
        cbcOpenRestriction d j inferInstance ⋙
          proEtaleRingModuleDirectImage j (d.completedRing T) (d.completedRing U)
            (d.integralRingIso j),
      ∀ (M : proEtaleRingModules T (d.completedRing T)) (V : T.ProEt)
        (x : M.val.obj (op V)),
        (η.app M).val.app (op V) x = M.val.map (cbcOpenProjection j V).op x := by
  refine ⟨(cbcRestrictionAdjunction d j).unit,
    cbcRestrictionAdjunction_unit d j, ?_⟩
  intro θ hθ
  ext M V x
  exact (hθ M V.unop x).trans (cbcRestrictionAdjunction_unit d j M V.unop x).symm

/-- The section-normalized restriction unit.
Source: Stacks 03DI (blueprint: thm-cbc-complete-proetale). -/
def cbcRestrictionUnit {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (cbcRestrictionUnit_existsUnique d j).choose

set_option maxHeartbeats 800000 in
-- Transposing the section unit compares the concrete and small-model module categories.
/-- Ordinary inverse image identifies with open restriction by transposing its section unit.
Source: Stacks 03DI and 09AE (blueprint: thm-cbc-complete-proetale). -/
def cbcPullToRestriction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j) ⟶ cbcOpenRestriction d j inferInstance :=
  (((proEtaleRingModuleAdjunction j (d.completedRing T) (d.completedRing U)
    (d.integralRingIso j)).whiskerRight
      (proEtaleRingModules T (d.completedRing T))).homEquiv
        (𝟭 (proEtaleRingModules T (d.completedRing T)))
          (cbcOpenRestriction d j inferInstance)).symm (cbcRestrictionUnit d j)

/-- The specified restriction comparison is invertible.
Source: Stacks 03DI and 09AE (blueprint: thm-cbc-complete-proetale).
Proof: the open-site adjunction, with its finite-projection-normalized coefficient maps,
lifts to an adjunction between restriction and direct image. Its unit has exactly the
specified section formula. Uniqueness of that unit identifies the displayed transpose
with the comparison between the two left adjoints to the same direct image. Uniqueness
of left adjoints makes this comparison invertible. -/
theorem cbcPullToRestriction_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcPullToRestriction d j) := by
  let a := proEtaleRingModuleAdjunction j (d.completedRing T) (d.completedRing U)
    (d.integralRingIso j)
  let b := cbcRestrictionAdjunction d j
  have hu : cbcRestrictionUnit d j = b.unit := by
    apply (cbcRestrictionUnit_existsUnique d j).unique
    · exact (cbcRestrictionUnit_existsUnique d j).choose_spec.1
    · exact cbcRestrictionAdjunction_unit d j
  have he : cbcPullToRestriction d j = (a.leftAdjointUniq b).hom := by
    apply (a.whiskerRight (proEtaleRingModules T (d.completedRing T))).homEquiv
      (𝟭 _) (cbcOpenRestriction d j inferInstance) |>.injective
    rw [cbcPullToRestriction, Equiv.apply_symm_apply, hu]
    apply NatTrans.ext
    funext M
    exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a b M).symm
  rw [he]
  infer_instance

/-- The exact, section-normalized open adjunction on completed coefficients.
Source: Stacks 03DI and 03DJ (blueprint: thm-cbc-complete-proetale). -/
def cbcDerivedOpenAdjunction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcDerivedOpenShriek d j inferInstance ⊣ d.pull j :=
  Adjunction.ofNatIsoRight
    ((Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
      (@asIso _ _ _ _ (cbcPullToRestriction d j)
        (cbcPullToRestriction_isIso d j)).symm).mapDerivedCategoryRightDerivedAdjunction)
    (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).rightDerivedFunctorIsoMapDerivedCategory

/-- Abbreviation for the recorded exact open extension, without a new construction.
Source: Stacks 03DI (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcJ {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  cbcDerivedOpenShriek d j inferInstance

/-- Open composition is the unique comparison of the composition adjunctions.
Source: Stacks 03DI, 0F7D (blueprint: thm-cbc-complete-proetale). -/
def cbcJComp {U V T : Scheme.{t}} (j : U ⟶ V) (k : V ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion k] : cbcJ d j ⋙ cbcJ d k ≅ cbcJ d (j ≫ k) :=
  Adjunction.leftAdjointCompIso (cbcDerivedOpenAdjunction d j)
    (cbcDerivedOpenAdjunction d k) (cbcDerivedOpenAdjunction d (j ≫ k))
    (d.pullComp j k).symm

/-- Equality transport for the recorded open extension.
Source: blueprint canonical comparisons (blueprint: thm-cbc-complete-proetale). -/
def cbcJCongr {U T : Scheme.{t}} {j k : U ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) : cbcJ d j ≅ cbcJ d k :=
  by
    subst k
    exact Iso.refl _

/-- Proper inverse image/direct image with their published tensor-normalized adjunction.
Source: Stacks 07A6 (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcPullPushAdjunction {U T : Scheme.{t}} (f : U ⟶ T) : d.pull f ⊣ d.push f :=
  proEtaleRingDerivedAdjunction f (d.completedRing T) (d.completedRing U)
    (d.integralRingIso f)

/-- Pullback composition around a commutative square, with its canonical compositors.
Source: Stacks 07A7 (blueprint: thm-cbc-complete-proetale). -/
def cbcSquarePull {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    d.pull i ⋙ d.pull r ≅ d.pull p ⋙ d.pull k :=
  (d.pullComp r i).symm ≪≫ eqToIso (congrArg (fun f ↦ d.pull f) h.symm) ≪≫
    d.pullComp k p

/-- The open unit is invertible, including on the empty open subscheme.
Source: Stacks 03DI (blueprint: thm-cbc-complete-proetale).
Proof: restriction of the extension presheaf has just the summand indexed by the
structure map of an object over the open. Sheafification and localization preserve
this unit identification, so every component of the derived unit is invertible. -/
theorem cbcOpenUnit_isIso {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    IsIso (cbcDerivedOpenAdjunction d j).unit := by
  let W := cbcOpenObject j inferInstance
  let e := ProEt.sliceEquiv T W
  let : e.inverse.IsDenseSubsite (ProEt.topology U) ((ProEt.topology T).over W) :=
    ProEt.sliceDense T W
  let : e.inverse.IsContinuous (ProEt.topology U) ((ProEt.topology T).over W) :=
    inferInstance
  let : e.functor.IsContinuous ((ProEt.topology T).over W) (ProEt.topology U) :=
    cbcSliceFunctor_continuous T W
  let : e.symm.functor.IsContinuous (ProEt.topology U) ((ProEt.topology T).over W) :=
    inferInstanceAs (e.inverse.IsContinuous _ _)
  let : e.symm.inverse.IsContinuous ((ProEt.topology T).over W) (ProEt.topology U) :=
    inferInstanceAs (e.functor.IsContinuous _ _)
  let : e.functor.IsDenseSubsite ((ProEt.topology T).over W) (ProEt.topology U) := by
    have h := e.eq_inducedTopology_of_isDenseSubsite
      ((ProEt.topology T).over W) (ProEt.topology U)
    rw [h]
    infer_instance
  let : e.symm.inverse.IsDenseSubsite ((ProEt.topology T).over W)
      (ProEt.topology U) := inferInstanceAs (e.functor.IsDenseSubsite _ _)
  let c := (sheafCompose ((ProEt.topology T).over W)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso
      (cbcCompletedRestriction W d)
  obtain ⟨q, hq⟩ := ProEt.module_transport (ProEt.topology U) ((ProEt.topology T).over W)
    e.symm (reductionModuleRing U (d.completedRing U))
    ((reductionModuleRing T (d.completedRing T)).over W) c
  let hq' : q.functor ≅ cbcModuleToSlice d T W :=
    Functor.fullyFaithfulCancelRight (SheafOfModules.forget _)
      (eqToIso (by rw [hq]; rfl))
  have : (cbcModuleToSlice d T W).IsEquivalence :=
    Functor.isEquivalence_of_iso hq'
  have : (cbcModuleToSlice d T W).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  have : (SheafOfModules.localizedModuleExtension.{t} (d.completedRing T) W).Additive :=
    SheafOfModules.localizedModuleExtension_additive (d.completedRing T) W
  have : PreservesFiniteLimits
      (SheafOfModules.localizedModuleExtension.{t} (d.completedRing T) W) :=
    SheafOfModules.localizedModuleExtension_limits (d.completedRing T) W
  have : PreservesFiniteColimits
      (SheafOfModules.localizedModuleExtension.{t} (d.completedRing T) W) :=
    SheafOfModules.localizedModuleExtension_colimits (d.completedRing T) W
  let b := SheafOfModules.localizedModuleDerivedAdjunction.{t}
    (d.completedRing T) W
  have : IsIso b.unit :=
    SheafOfModules.localizedDerivedUnit_isIso j (d.completedRing T)
  have := b.fullyFaithfulLOfIsIsoUnit.full
  have := b.fullyFaithfulLOfIsIsoUnit.faithful
  let eD := Functor.mapDerivedCategoryCompIso (cbcModuleToSlice d T W)
    (SheafOfModules.localizedModuleExtension (d.completedRing T) W)
  have : (cbcJ d j).Full := Functor.Full.of_iso eD.symm
  have : (cbcJ d j).Faithful := Functor.Faithful.of_iso eD.symm
  infer_instance

/-- The inverse open comparison is the transpose of the open-extension unit.
Source: Stacks 09AE and 07A7 (blueprint: thm-cbc-complete-proetale). -/
def cbcBetaInv {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g) :
    d.pull a ⋙ cbcJ d j' ⟶ cbcJ d j ⋙ d.pull g :=
  (((cbcDerivedOpenAdjunction d j').whiskerRight _).homEquiv _ _).symm
    ((Functor.leftUnitor (d.pull a)).inv ≫
      Functor.whiskerRight (cbcDerivedOpenAdjunction d j).unit (d.pull a) ≫
      (Functor.associator (cbcJ d j) (d.pull j) (d.pull a)).hom ≫
      Functor.whiskerLeft (cbcJ d j) (cbcSquarePull d a j' j g h).inv ≫
      (Functor.associator (cbcJ d j) (d.pull g) (d.pull j')).inv)

/-- The unit-normalized open comparison is invertible for a Cartesian open square.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale).
Proof: ordinary open base change identifies the target with an object in the essential
image of the fully faithful open extension. The open counit at that target is therefore
invertible. The transpose in the definition is the pulled-back open unit followed by
the square compositor, both invertible. Its inverse transpose is extension applied to
that isomorphism followed by the invertible counit. -/
theorem cbcBetaInv_isIso {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (_sq : IsPullback a j' j g) : IsIso (cbcBetaInv d a j' j g h) := by
  let sq : OpenImmersionSquare a j' j g :=
    { w := h
      isoPullback := _sq.isoPullback
      hom_fst := _sq.isoPullback_hom_fst
      hom_snd := _sq.isoPullback_hom_snd
      isOpenImmersion := inferInstance
      isOpenImmersion' := inferInstance }
  have := cbcOpenUnit_isIso d j
  have := cbcOpenUnit_isIso d j'
  let ff := (cbcDerivedOpenAdjunction d j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have he : IsIso (cbcDatumOrdinaryExchange d sq) := by
    unfold cbcDatumOrdinaryExchange cbcOrdinaryExchange
    infer_instance
  let adj := (cbcDerivedOpenAdjunction d j').whiskerRight (d.derived U)
  have : IsIso (adj.counit.app (cbcJ d j ⋙ d.pull g)) :=
    adj.isIso_counit_app_of_iso (asIso (cbcDatumOrdinaryExchange d sq))
  unfold cbcBetaInv
  rw [Adjunction.homEquiv_counit]
  infer_instance


/-- Cartesian open comparison, in the forward direction fixed by the inverse unit-mate.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale). -/
def cbcBeta {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) : cbcJ d j ⋙ d.pull g ≅ d.pull a ⋙ cbcJ d j' :=
  (@asIso _ _ _ _ (cbcBetaInv d a j' j g h)
    (cbcBetaInv_isIso d a j' j g h sq)).symm

/-- Open extension to direct image, fixed by the ordinary units of both adjunctions.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale). -/
def cbcOpenToPush {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcJ d j ⟶ d.push j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (cbcJ d j) (cbcPullPushAdjunction d j).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (@inv _ _ _ _ (cbcDerivedOpenAdjunction d j).unit
      (cbcOpenUnit_isIso d j)) (d.push j) ≫ (Functor.leftUnitor _).hom

private theorem cbcRestrictionScalar_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcCompletedRestrictionMap d j inferInstance) := by
  let G := cbcOpenSiteFunctor j inferInstance
  let R := d.completedRing T
  let c := cbcCompletedRestrictionMap d j inferInstance
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{t + 1})
    (ProEt.topology U) (ProEt.topology T)
  let e := ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).leftAdjointUniq b).app R
  have hc : (d.integralRingIso j).hom ≫ c = e.hom := by
    apply ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv _ _).injective
    change ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv R
      ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj R)) ((d.integralRingIso j).hom ≫ c) =
      ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv R
        ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
          (ProEt.topology U) (ProEt.topology T)).obj R))
        (((proEtaleSheafAdjunction j CommRingCat.{t + 1}).leftAdjointUniq b).hom.app R)
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    apply Sheaf.hom_ext
    exact (cbcCompletedCoefficientCounit d j).symm
  have heq : c = ((d.integralRingIso j).symm ≪≫ e).hom := by
    apply (cancel_epi (d.integralRingIso j).hom).1
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc] using hc
  change IsIso c
  rw [heq]
  infer_instance

private theorem cbcClopenReverseAdjunction {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [IsClosedImmersion j] : Nonempty (d.pull j ⊣ cbcJ d j) := by
  let R := d.completedRing T
  let S := d.completedRing U
  let c := cbcCompletedRestrictionMap d j inferInstance
  have : IsIso c := cbcRestrictionScalar_isIso d j
  let : (proEtaleOpenComposition j).IsContinuous (ProEt.topology U)
      (ProEt.topology T) := cbcOpenSiteFunctor_continuous j inferInstance
  obtain ⟨b⟩ := clopenScalarRestrictionReverseAdjunction j R S (asIso c)
    (cbcOpenShriek d j inferInstance) (cbcOpenAdjunction d j inferInstance)
  let pb := proEtaleRingModulePullback j R S (d.integralRingIso j)
  let r : pb ≅ cbcOpenRestriction d j inferInstance :=
    @asIso _ _ _ _ (cbcPullToRestriction d j) (cbcPullToRestriction_isIso d j)
  let br := b.ofNatIsoLeft r.symm
  let : (cbcOpenShriek d j inferInstance).Additive :=
    cbcOpenShriek_additive d j inferInstance
  let : PreservesFiniteLimits (cbcOpenShriek d j inferInstance) :=
    cbcOpenShriek_finiteLimits d j inferInstance
  let : PreservesFiniteColimits (cbcOpenShriek d j inferInstance) :=
    cbcOpenShriek_finiteColimits d j inferInstance
  exact ⟨br.mapExactDerivedCategory⟩

/-- The specified open-to-direct-image map is invertible on a clopen immersion.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale).
Proof: split every test object into its two clopen parts. Both extension and direct
image give the sections on the image part and zero on the complement. The units in
the definition identify the comparison with identity on that first factor. The same
formula holds on complexes and descends through the exact localizations. -/
theorem cbcOpenToPush_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [IsClosedImmersion j] : IsIso (cbcOpenToPush d j) := by
  obtain ⟨ar⟩ := cbcClopenReverseAdjunction d j
  let e := ar.rightAdjointUniq (cbcPullPushAdjunction d j)
  have := cbcOpenUnit_isIso d j
  let ff := (cbcDerivedOpenAdjunction d j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (d.push j).Full := Functor.Full.of_iso e
  have : (d.push j).Faithful := Functor.Faithful.of_iso e
  have hi (M : d.derived U) : IsIso ((cbcOpenToPush d j).app M) := by
    have hu : IsIso ((cbcPullPushAdjunction d j).unit.app ((cbcJ d j).obj M)) :=
      (cbcPullPushAdjunction d j).isIso_unit_app_of_iso (e.app M)
    dsimp only [cbcOpenToPush, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app]
    simp only [Category.id_comp]
    have hv : IsIso ((inv (cbcDerivedOpenAdjunction d j).unit).app M) := inferInstance
    have hw : IsIso ((d.push j).map ((inv (cbcDerivedOpenAdjunction d j).unit).app M)) :=
      inferInstance
    exact IsIso.comp_isIso' hu (IsIso.comp_isIso' hw (IsIso.id _))
  exact NatIso.isIso_of_isIso_app _

/-- Canonical clopen projection; identity on the image and zero on the complement.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale). -/
def cbcClopenProjection {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [IsClosedImmersion j] : 𝟭 (d.derived T) ⟶ d.pull j ⋙ cbcJ d j :=
  (cbcPullPushAdjunction d j).unit ≫ Functor.whiskerLeft (d.pull j)
    (@inv _ _ _ _ (cbcOpenToPush d j) (cbcOpenToPush_isIso d j))

/-- The non-Cartesian proper/open comparison before taking its proper-adjunction mate.
It projects onto the clopen image of (k,r) in the fibre product, with no extra
Cartesian-square hypothesis on a refinement.
Source: Stacks 0F7B, 07A7 (blueprint: thm-cbc-complete-proetale). -/
def cbcProperOpenAlpha {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : cbcJ d i ⋙ d.pull p ⟶ d.pull r ⋙ cbcJ d k :=
  (cbcBeta d (pullback.snd p i) (pullback.fst p i) i p
    pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (d.pull (pullback.snd p i))
    (cbcClopenProjection d (ProEtale.StrictTower.squareLift k r p i h)))
      (cbcJ d (pullback.fst p i)) ≫
  Functor.whiskerRight (Functor.associator (d.pull (pullback.snd p i))
    (d.pull (ProEtale.StrictTower.squareLift k r p i h))
      (cbcJ d (ProEtale.StrictTower.squareLift k r p i h))).inv
        (cbcJ d (pullback.fst p i)) ≫
  (Functor.associator (d.pull (pullback.snd p i) ⋙
    d.pull (ProEtale.StrictTower.squareLift k r p i h))
      (cbcJ d (ProEtale.StrictTower.squareLift k r p i h))
        (cbcJ d (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (d.pull (pullback.snd p i) ⋙
    d.pull (ProEtale.StrictTower.squareLift k r p i h))
      ((cbcJComp d (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
        (cbcJCongr d (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight ((d.pullComp (ProEtale.StrictTower.squareLift k r p i h)
    (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (fun f ↦ d.pull f) (pullback.lift_snd k r h))).hom) (cbcJ d k)

/-- The canonical proper/open map is the proper-adjunction mate of the clopen projection.
Source: Stacks 0F7B, 07A7 (blueprint: thm-cbc-complete-proetale). -/
def cbcProperOpenGamma {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : d.push r ⋙ cbcJ d i ⟶ cbcJ d k ⋙ d.push p :=
  mateEquiv (cbcPullPushAdjunction d r) (cbcPullPushAdjunction d p)
    (cbcProperOpenAlpha d k r p i h)

/-- The base-changed finite-type morphism is quasi-compact. This is a consequence
of the supplied square, not an additional typeclass hypothesis in the coherence laws.
Source: Stacks 01K5 (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcBaseChangeQuasiCompact {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sq : OpenImmersionSquare g' c'.i c.i gbar) : QuasiCompact f' :=
  c'.quasiCompact (MorphismProperty.of_isPullback
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
      (c.quasiCompact_openImmersion inferInstance))

/-- The recorded exchange, with its quasi-compactness instance named for explicit
transport to a base-changed compactification. Its map is definitionally unchanged.
Source: blueprint ordered two-factor composite (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcExchange {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [qf : QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :=
  completedCompactSupportExchange d c c' gbar sp sj r a ha K

/-- The exact chosen-compactification functor Rp_* j_! on completed-ring modules.
Source: blueprint displayed definition of Rf_!^c (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcSupport {X Y : Scheme.{t}} {f : X ⟶ Y} (c : Compactification f) :=
  cbcJ d c.i ⋙ d.push c.g

section

attribute [local irreducible] cbcDerivedOpenShriek cbcProperOpenGamma
  AdicCoefficientDatum.pushComp AdicCoefficientDatum.pushId HasDerivedCategory.standard

/-- The canonical proper/open refinement comparison as a natural transformation.
Its components are the proper pushforward of gamma, preceded by the inverse proper
identity comparison and followed by the proper composition comparison. Explicit
unitors and associators have identity components, so this construction gives the
same component formula as the canonical refinement map.
Source: blueprint proof step 8, C_u; Stacks 0F7B and 0F7C
(blueprint: def-cbc-completed-refinement-transformation). -/
@[irreducible]
def cbcRefinementTransformation
    {X Y : Scheme.{t}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) :
    cbcSupport d c₂ ⟶ cbcSupport d c₁ := by
  let : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion inferInstance
  let : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion inferInstance
  let e₁ := Functor.whiskerRight (d.pushId X).inv (cbcJ d c₂.i)
  let e₂ := cbcProperOpenGamma d c₁.i (𝟙 X) u.hom c₂.i
    (u.i_hom.trans (Category.id_comp _).symm)
  exact Functor.whiskerRight (Functor.leftUnitor (cbcJ d c₂.i)).inv (d.push c₂.g) ≫
    Functor.whiskerRight (e₁ ≫ e₂) (d.push c₂.g) ≫
    (Functor.associator (cbcJ d c₁.i) (d.push u.hom) (d.push c₂.g)).hom ≫
    Functor.whiskerLeft (cbcJ d c₁.i) (d.pushComp u.hom c₂.g).hom ≫
    Functor.whiskerLeft (cbcJ d c₁.i)
      (eqToIso (congrArg (fun f ↦ d.push f) u.hom_g)).hom

end

/-- The canonical refinement map, directed from the coarser to the finer compactification.
It is proper pushforward of gamma, with the proper identity and composition comparisons.
Source: blueprint proof step 8, C_u (blueprint: thm-cbc-complete-proetale). -/
def cbcRefinementMap {X Y : Scheme.{t}} {f : X ⟶ Y} [qf : QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (K : d.derived X) :
    (cbcSupport d c₂).obj K ⟶ (cbcSupport d c₁).obj K :=
  (cbcRefinementTransformation d u).app K

/-- The compatible-tower compact-support composition map. Its middle factor is the
specified proper/open gamma, so this is not an arbitrary isomorphism of the endpoints.
Source: blueprint proof step 8, D_j (blueprint: thm-cbc-complete-proetale). -/
def cbcCompositionMap {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [qh : QuasiCompact h]
    (cf : Compactification f) (ch : Compactification h) (chf : Compactification (f ≫ h))
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
    [IsOpenImmersion b] [QuasiCompact b] [IsProper p]
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g) (K : d.derived X) :
    (cbcSupport d ch).obj ((cbcSupport d cf).obj K) ⟶ (cbcSupport d chf).obj K :=
  letI : QuasiCompact ch.i := ch.quasiCompact_openImmersion inferInstance
  (d.push ch.g).map ((cbcProperOpenGamma d b cf.g p ch.i hp).app
      ((cbcJ d cf.i).obj K)) ≫
    (d.pushComp p ch.g).hom.app ((cbcJ d b).obj ((cbcJ d cf.i).obj K)) ≫
    (d.push (p ≫ ch.g)).map
      ((cbcJComp d cf.i b).hom.app K ≫ (cbcJCongr d hb).hom.app K) ≫
    (eqToIso (congrArg (fun f ↦ d.push f) hq)).hom.app ((cbcJ d chf.i).obj K)

/-- Composition for a supplied Cartesian compatible tower. The open immersion and
quasi-compactness of b are derived from that square and the outer compactification.
Source: blueprint proof step 8, compatible towers (blueprint: thm-cbc-complete-proetale). -/
def cbcTowerCompositionMap {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [qh : QuasiCompact h]
    (cf : Compactification f) (ch : Compactification h) (chf : Compactification (f ≫ h))
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z) [IsProper p]
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g) (sq : IsPullback b cf.g p ch.i) (K : d.derived X) :
    (cbcSupport d ch).obj ((cbcSupport d cf).obj K) ⟶ (cbcSupport d chf).obj K :=
  letI : IsOpenImmersion b := MorphismProperty.of_isPullback sq.flip ch.isOpenImmersion
  letI : QuasiCompact b := MorphismProperty.of_isPullback sq.flip
    (ch.quasiCompact_openImmersion qh)
  cbcCompositionMap d cf ch chf b p hb hp hq K

private theorem cbcTowerComplete_of_property (T : Scheme.{t})
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : d.derived T) (hK : cbcCompleteProperty d T r a ha K) :
    d.TowerComplete T K := by
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)
  change IsIso (intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)) at hK
  change IsIso (d.completionUnit T K)
  change intrinsicCompletionUnit T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K) ≫
      c.hom = d.completionUnit T K at hc
  rw [← hc]
  infer_instance

private theorem cbcCompletedExchange_naturality
    {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {K H : d.derived X} (k : K ⟶ H) :
    (d.completedPull g).map ((d.push f).map k) ≫ d.completedExchange sq H =
      d.completedExchange sq K ≫ (d.push f').map ((d.completedPull g').map k) := by
  let π : d.push f ⋙ completedReductionTower Y d ≅
      completedReductionTower X d ⋙ d.towerPush f :=
    NatIso.ofComponents (fun K ↦ asIso (d.towerProjection f K))
      (fun {K H} k ↦ (d.towerProjection_properties f K).2.1 H k)
  let e : d.push f ⋙ d.completedPull g ⟶ d.completedPull g' ⋙ d.push f' :=
    Functor.whiskerRight (Functor.whiskerRight π.hom (d.towerPull g))
      (completedRlim Y' (d.completedRing Y')) ≫
        Functor.whiskerRight (exchangeStrictNatTrans d sq)
          (completedRlim Y' (d.completedRing Y')) ≫
        Functor.whiskerLeft (completedReductionTower X d ⋙ d.towerPull g')
          (d.directImageRlimIso f').inv
  exact e.naturality k

/-- The completed compact-support exchange is invertible on an intrinsically complete
object carrying compatible bounded-below etale origins. Its component is the ordered
proper exchange followed by the normalized completed open comparison from
`completedCompactSupportExchange`. No common lower bound on the origins is required.
The remaining clauses of this node are stated in the identity, horizontal,
compactifications, refinement, vertical, and composition_refinement theorems below.

Source: blueprint thm-cbc-complete-proetale, proof steps 1--8; Stacks 09AE, 09AF,
09BP, 099M, 099N, 09C9 and 07A7 (blueprint: thm-cbc-complete-proetale).
Proof:
1. Localize the ringed site at the open. Restriction is evaluation on the localized
objects, so commutes with limits and identifies the restricted completed coefficient
ring with A_X. The localized module adjunction supplies the actual exact j_! used here.
2. Resolve each positive quotient by a bounded finite-projective A-complex. The open
projection formula identifies reductions of j_!K with j_!K_n, naturally in the quotient
maps. Finite-coefficient site comparison extends each retained etale origin; exact etale
extension preserves its own lower bound. These origins remain transition-compatible.
3. The ringed open/closed sequence and immersion limit preservation imply that j_!
preserves small limits. Countable products are exact. On K-injective tower complexes,
the canonical comparison j_! lim I -> lim J is induced by the resolution j_!I -> J.
The signed Roos map lim C -> Cone(1-shift)[-1], x |-> (0,x), commutes with this map
and the diagonal product map. The latter is a quasi-isomorphism, hence the comparison
is invertible. The same formulas preserve homotopies, so resolution comparison makes
it natural and independent of choices. The quotient-unit family maps to the extended
quotient-unit family; Koszul reconstruction therefore proves j_!K complete.
4. Apply completed proper base change to p and j_!K, using steps 2 and 3. Proper
direct image commutes with the relevant derived limits, identifies its reduction tower,
and preserves completeness. This proves invertibility of the first exchange factor.
5. The second factor is the finite-reduction comparison, Rlim of the normalized open
unit-mate, and the inverse of the extension/Rlim comparison of step 3, in that order.
Every factor is invertible. Completed pullback preserves completeness, so the target
comparison applies as well. Their ordered composite is precisely the map displayed here.
6. Normalize the full strict-tower exchange as the proper mate followed by the open
unit-mate, then restrict to constant A coefficients. These are equalities of tower
morphisms before evaluation, and the completed comparison is their Rlim transport.
7. Naturality follows from the mates and comparisons. Identity and horizontal pasting
hold before evaluation by mate-pasting and the open unit characterization. Applying
Rlim cancels adjacent reconstruction comparisons and leaves the canonical completed
identity and composition identifications displayed in the following statements.
8. Use the normalized proper/open comparison for every commutative proper/open square,
including noncartesian refinement squares. Its finite-origin components are invertible;
the reduction cone criterion and completeness give invertibility after completion.
Mate-pasting gives the refinement cocycle, base-change/refinement interchange, vertical
composition, and compatibility with refining compatible towers. Cofiltered common
refinements of compactifications and compatible towers remove both choices. Proper
composition and the same Rlim comparisons give exactly the equations below. -/
theorem completeCompactSupportProetale_isIso
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    IsIso (completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha K) ∧
      ∀ (H : (cbcCompleteProperty d X r a ha).FullSubcategory)
        (k : K.obj ⟶ H.obj),
        (d.completedPull g).map
            ((d.push c.g).map
              ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).map k)) ≫
            completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha H =
          completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha K ≫
            (d.push c'.g).map
              ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).map
                ((d.completedPull g').map k)) := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hopen := completedOpenExchangeComparison d openSquare r a ha
  have hJ := (hopen.2 K).1
  obtain ⟨W⟩ := ringedOrigins X d K.obj _origins
  obtain ⟨WJ⟩ := cbcCompletedOpenFiniteEtaleOrigins d c.i K.obj W
  have hT := cbcTowerComplete_of_property d c.Z r a ha _ hJ
  have := completedExchange_isIso_of_towerComplete d properSquare _ hT WJ
  have := hopen.1
  constructor
  · unfold completedCompactSupportExchange
    infer_instance
  · intro H k
    have hproper := cbcCompletedExchange_naturality d properSquare
      ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).map k)
    have hopenNat := (cbcDatumCompletedExchange d openSquare r a ha).naturality
      (ObjectProperty.homMk k)
    change (d.completedPull gbar).map ((cbcDerivedOpenShriek d c.i
      c.isOpenImmersion).map k) ≫ (cbcDatumCompletedExchange d openSquare r a ha).app H =
        (cbcDatumCompletedExchange d openSquare r a ha).app K ≫
          (cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).map
            ((d.completedPull g').map k) at hopenNat
    unfold completedCompactSupportExchange
    simp only [Category.assoc]
    rw [← Category.assoc, hproper, Category.assoc, ← Functor.map_comp, hopenNat]
    simp only [Functor.map_comp]


private theorem cbcCompletedOpenIdentity {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [QuasiCompact j]
    (sq : OpenImmersionSquare (𝟙 U) j j (𝟙 T))
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d U r a ha).FullSubcategory)
    (hK : d.TowerComplete U K.obj)
    (hJ : d.TowerComplete T ((cbcJ d j).obj K.obj)) :
    (cbcDatumCompletedExchange d sq r a ha).app K ≫
        (cbcJ d j).map (d.completedPullId U K.obj hK).hom =
      (d.completedPullId T ((cbcJ d j).obj K.obj) hJ).hom := by
  apply ((d.completedPull_reflection (𝟙 T)).2 ((cbcJ d j).obj K.obj) _ hJ).1
  dsimp only
  rw [← Category.assoc, cbcDatumCompletedExchange_unit]
  rw [Category.assoc, ← Functor.map_comp]
  have hU := (d.completedPullId_existsUnique U K.obj hK).choose_spec.1
  change d.ordinaryToCompleted (𝟙 U) K.obj ≫
    (d.completedPullId U K.obj hK).hom = (d.pullId U).hom.app K.obj at hU
  rw [hU]
  exact (cbcDatumOrdinaryExchange_identity d j sq K.obj).trans
    ((d.completedPullId_existsUnique T ((cbcJ d j).obj K.obj) hJ).choose_spec.1).symm

/-- Identity base change is the identity after the canonical completed identity maps.
The existential proofs only supply the complete-object inputs of those fixed maps.
Source: blueprint statement and proof step 7; Stacks 07A7, 099N
(blueprint: thm-cbc-complete-proetale).
Proof: write the exchange as Rlim of the proper mate followed by the open unit-mate.
Both identity mates are identities before evaluation. The quotient reconstruction and
open/limit comparisons preserve their units. Their conjugation is therefore precisely
the completed identity isomorphism displayed here, on K and on Rp_*j_!K. -/
theorem completeCompactSupportProetale_identity
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
    (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    ∃ (hK : d.TowerComplete X K.obj)
      (hF : d.TowerComplete Y ((cbcSupport d c).obj K.obj)),
      cbcExchange d c c (𝟙 c.Z) sp sj r a ha K ≫
          (cbcSupport d c).map (d.completedPullId X K.obj hK).hom =
        (d.completedPullId Y ((cbcSupport d c).obj K.obj) hF).hom := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hK := cbcTowerComplete_of_property d X r a ha K.obj K.property
  have hJp := (completedOpenExchangeComparison d sj r a ha).2 K |>.1
  have hJ := cbcTowerComplete_of_property d c.Z r a ha _ hJp
  have hF := d.push_complete c.g ((cbcJ d c.i).obj K.obj) hJ
  obtain ⟨W⟩ := ringedOrigins X d K.obj _origins
  obtain ⟨WJ⟩ := cbcCompletedOpenFiniteEtaleOrigins d c.i K.obj W
  have hp := d.completedExchange_identity_horizontal c.g sp
    ((cbcJ d c.i).obj K.obj) hJ WJ
  change d.completedExchange sp ((cbcJ d c.i).obj K.obj) = _ at hp
  have ho := cbcCompletedOpenIdentity d c.i sj r a ha K hK hJ
  refine ⟨hK, hF, ?_⟩
  change (d.completedExchange sp ((cbcJ d c.i).obj K.obj) ≫
      (d.push c.g).map ((cbcDatumCompletedExchange d sj r a ha).app K)) ≫
    (d.push c.g).map ((cbcJ d c.i).map (d.completedPullId X K.obj hK).hom) = _
  rw [hp]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [ho]
  simp


/-- Successive arbitrary base changes agree with the composite base change.
The intermediate completed pullback is complete; its proof is supplied in the conclusion
rather than assumed. The two completed pullback compositors have their unit normalization.
Source: blueprint statement and proof step 7; Stacks 07A7, 099N
(blueprint: thm-cbc-complete-proetale).
Proof: the strict-tower proper mate satisfies horizontal mate-pasting. Transpose the two
open comparisons; their transposes are the same iterated open unit, so beta satisfies the
same pasting equation. Substitute in the ordered two-factor exchange and move the middle
beta by naturality. Apply Rlim and cancel adjacent reconstruction comparisons. The
remaining outside comparisons are exactly d.completedPullComp, giving this equation.
Completed pullback preserves completeness by quotient/Koszul reconstruction. -/
theorem completeCompactSupportProetale_horizontal
    {X X' X'' Y Y' Y'' : Scheme.{t}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
    (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
    (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
    (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
    (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
    (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
    (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
    (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    ∃ hK' : cbcCompleteProperty d X' r a ha ((d.completedPull g').obj K.obj),
      cbcExchange d c c'' (hb ≫ gb) sp sj r a ha K =
        (d.completedPullComp h g).hom.app ((cbcSupport d c).obj K.obj) ≫
          (d.completedPull h).map (cbcExchange d c c' gb sp₁ sj₁ r a ha K) ≫
          cbcExchange d (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
            c' c'' hb sp₂ sj₂ r a ha ⟨(d.completedPull g').obj K.obj, hK'⟩ ≫
          (cbcSupport d c'').map ((d.completedPullComp h' g').inv.app K.obj) := by
  sorry

/-- Every normalized proper/open refinement map is invertible on the stated inputs.
No Cartesian hypothesis is imposed on the refinement square.
Source: blueprint statement and proof step 8; Stacks 0F7B, 09C9
(blueprint: thm-cbc-complete-proetale).
Proof: pass to the strict quotient tower after constant-coefficient restriction. The
section and unit normalizations identify gamma with the strict proper/open gamma.
Finite evaluation is the normalized finite-coefficient proper/open map on the retained
bounded-below origins, hence invertible by finite compact-support base change. The
cone is acyclic levelwise, so gamma is invertible as an actual derived strict-tower
map. Apply Rlim and the specified open/limit and proper composition comparisons. -/
theorem cbcRefinementMap_isIso
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    IsIso (cbcRefinementMap d u K.obj) := by
  sorry

/-- The canonical compactification comparison through any supplied common refinement.
Its factors are the specified proper/open refinement maps, not chosen endpoint isos.
Source: blueprint proof step 8, I_12 (blueprint: thm-cbc-complete-proetale). -/
def cbcCompactificationComparison
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₀ c₁ c₂ : Compactification f} (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    (cbcSupport d c₁).obj K.obj ≅ (cbcSupport d c₂).obj K.obj :=
  @asIso _ _ _ _ (cbcRefinementMap d u₁ K.obj)
      (cbcRefinementMap_isIso d u₁ r a ha K origins) ≪≫
    (@asIso _ _ _ _ (cbcRefinementMap d u₂ K.obj)
      (cbcRefinementMap_isIso d u₂ r a ha K origins)).symm

private theorem cbcRefinementMap_naturality
    {X Y : Scheme.{t}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂)
    {K H : d.derived X} (k : K ⟶ H) :
    (cbcSupport d c₂).map k ≫ cbcRefinementMap d u H =
      cbcRefinementMap d u K ≫ (cbcSupport d c₁).map k := by
  exact (cbcRefinementTransformation d u).naturality k

/-- Composition law for two section-normalized refinement components.
Source: Stacks 0F7D and blueprint step 8 (blueprint: lem-cbc-completed-refinement-map-composition).
Proof: paste the proper/open mates for two refinements, then use naturality of the
proper direct-image compositor. The intermediate direct-image identity comparison
cancels with its inverse and associativity leaves the displayed ordered composite.
-/
theorem cbcRefinementMap_composition_component
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (K : d.derived X)
    (c₁ c₂ c₃ : Compactification f) (u : c₁.Refinement c₂) (v : c₂.Refinement c₃) :
    cbcRefinementMap d (u.comp v) K =
      cbcRefinementMap d v K ≫ cbcRefinementMap d u K := by
  sorry

private theorem cbcMate_isIso
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) [L₁.IsEquivalence] [L₂.IsEquivalence] [IsIso α] :
    IsIso (mateEquiv adj₁ adj₂ α) := by
  dsimp only [mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk, TwoSquare.natTrans]
  infer_instance

section

attribute [local irreducible] cbcDerivedOpenShriek cbcProperOpenGamma
  cbcDerivedOpenAdjunction
  AdicCoefficientDatum.pullComp AdicCoefficientDatum.pullId
  AdicCoefficientDatum.pushComp AdicCoefficientDatum.pushId HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1600000 in
-- The concrete derived categories make the kernel check of the iso composites expensive.
/-- Identity law for the section-normalized refinement component.
Source: Stacks 0F7C and blueprint step 8 (blueprint: lem-cbc-completed-refinement-map-identity).
Proof: expand the normalized proper/open mate for the identity refinement. The identity
mate and the proper identity compositor cancel the inserted direct-image unit, leaving
`𝟙`; this is an equality of the concrete component on every derived input.
-/
theorem cbcRefinementMap_identity_component
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (K : d.derived X)
    (c : Compactification f) :
    cbcRefinementMap d (Compactification.Refinement.id c) K = 𝟙 _ := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have hpull {V W : Scheme.{t}} (e : V ⟶ W) [IsIso e] :
      (d.pull e).IsEquivalence := by
    let η : 𝟭 (d.derived W) ≅ d.pull e ⋙ d.pull (inv e) :=
      (d.pullId W).symm ≪≫
        eqToIso (congrArg (fun k ↦ d.pull k) (IsIso.inv_hom_id e).symm) ≪≫
          d.pullComp (inv e) e
    let ε : d.pull (inv e) ⋙ d.pull e ≅ 𝟭 (d.derived V) :=
      (d.pullComp e (inv e)).symm ≪≫
        eqToIso (congrArg (fun k ↦ d.pull k) (IsIso.hom_inv_id e)) ≪≫ d.pullId V
    exact (CategoryTheory.Equivalence.mk (d.pull e) (d.pull (inv e)) η ε).isEquivalence_functor
  let hs : c.i ≫ 𝟙 c.Z = 𝟙 X ≫ c.i := by simp
  let s := ProEtale.StrictTower.squareLift c.i (𝟙 X) (𝟙 c.Z) c.i hs
  have : IsIso s := by
    have : IsIso (s ≫ pullback.snd (𝟙 c.Z) c.i) := by
      change IsIso (pullback.lift c.i (𝟙 X) hs ≫ pullback.snd _ _)
      rw [pullback.lift_snd]
      infer_instance
    exact IsIso.of_isIso_comp_right s (pullback.snd (𝟙 c.Z) c.i)
  have : (d.pull s).IsEquivalence := hpull s
  have : (d.push s).IsEquivalence :=
    (cbcPullPushAdjunction d s).isEquivalence_right_of_isEquivalence_left
  have : IsIso (cbcOpenToPush d s) := cbcOpenToPush_isIso d s
  have : IsIso ((cbcPullPushAdjunction d s).unit) := by infer_instance
  have hproj : IsIso (cbcClopenProjection d s) := by
    change IsIso ((cbcPullPushAdjunction d s).unit ≫ _)
    exact IsIso.comp_isIso' (inferInstanceAs (IsIso (cbcPullPushAdjunction d s).unit))
      (Functor.isoWhiskerLeft (d.pull s)
        (@asIso _ _ _ _ (cbcOpenToPush d s) (cbcOpenToPush_isIso d s)).symm).isIso_hom
  have hα : IsIso (cbcProperOpenAlpha d c.i (𝟙 X) (𝟙 c.Z) c.i hs) := by
    unfold cbcProperOpenAlpha
    exact ((cbcBeta d (pullback.snd (𝟙 c.Z) c.i)
        (pullback.fst (𝟙 c.Z) c.i) c.i (𝟙 c.Z)
        pullback.condition.symm (IsPullback.of_hasPullback _ _).flip) ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (d.pull (pullback.snd (𝟙 c.Z) c.i))
          (@asIso _ _ _ _ (cbcClopenProjection d s) hproj))
        (cbcJ d (pullback.fst (𝟙 c.Z) c.i)) ≪≫
      Functor.isoWhiskerRight
        (Functor.associator (d.pull (pullback.snd (𝟙 c.Z) c.i)) (d.pull s)
          (cbcJ d s)).symm (cbcJ d (pullback.fst (𝟙 c.Z) c.i)) ≪≫
      Functor.associator (d.pull (pullback.snd (𝟙 c.Z) c.i) ⋙ d.pull s)
        (cbcJ d s) (cbcJ d (pullback.fst (𝟙 c.Z) c.i)) ≪≫
      Functor.isoWhiskerLeft (d.pull (pullback.snd (𝟙 c.Z) c.i) ⋙ d.pull s)
        (cbcJComp d s (pullback.fst (𝟙 c.Z) c.i) ≪≫
          cbcJCongr d (pullback.lift_fst c.i (𝟙 X) hs)) ≪≫
      Functor.isoWhiskerRight
        ((d.pullComp s (pullback.snd (𝟙 c.Z) c.i)).symm ≪≫
          eqToIso (congrArg (fun k ↦ d.pull k) (pullback.lift_snd c.i (𝟙 X) hs)))
        (cbcJ d c.i)).isIso_hom
  have : (d.pull (𝟙 X)).IsEquivalence := hpull (𝟙 X)
  have : (d.pull (𝟙 c.Z)).IsEquivalence := hpull (𝟙 c.Z)
  have : IsIso (cbcProperOpenAlpha d c.i (𝟙 X) (𝟙 c.Z) c.i hs) := hα
  have hγ : IsIso (cbcProperOpenGamma d c.i (𝟙 X) (𝟙 c.Z) c.i hs) := by
    unfold cbcProperOpenGamma
    exact @cbcMate_isIso _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (cbcPullPushAdjunction d (𝟙 X)) (cbcPullPushAdjunction d (𝟙 c.Z))
      (cbcProperOpenAlpha d c.i (𝟙 X) (𝟙 c.Z) c.i hs)
      (hpull (𝟙 X)) (hpull (𝟙 c.Z)) hα
  have : IsIso (cbcProperOpenGamma d c.i (𝟙 X) (𝟙 c.Z) c.i hs) := hγ
  have hi : IsIso (cbcRefinementMap d (Compactification.Refinement.id c) K) := by
    have ht : IsIso (cbcRefinementTransformation d (Compactification.Refinement.id c)) := by
      unfold cbcRefinementTransformation
      dsimp only [Compactification.Refinement.id]
      exact (Functor.isoWhiskerRight (Functor.leftUnitor (cbcJ d c.i)).symm (d.push c.g) ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerRight (d.pushId X).symm (cbcJ d c.i) ≪≫
            @asIso _ _ _ _ (cbcProperOpenGamma d c.i (𝟙 X) (𝟙 c.Z) c.i hs) hγ)
          (d.push c.g) ≪≫
        Functor.associator (cbcJ d c.i) (d.push (𝟙 c.Z)) (d.push c.g) ≪≫
        Functor.isoWhiskerLeft (cbcJ d c.i) (d.pushComp (𝟙 c.Z) c.g) ≪≫
        Functor.isoWhiskerLeft (cbcJ d c.i)
          (eqToIso (congrArg (fun k ↦ d.push k) (Category.id_comp c.g)))).isIso_hom
    exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ ht K
  have h := cbcRefinementMap_composition_component d K c c c
    (Compactification.Refinement.id c) (Compactification.Refinement.id c)
  rw [Compactification.Refinement.id_comp] at h
  apply (cancel_mono (cbcRefinementMap d (Compactification.Refinement.id c) K)).mp
  simpa only [Category.id_comp] using h.symm

end


/-- The canonical refinement maps preserve units and composition on every ambient input.
Source: Stacks 0F7C and 0F7D, proper/open mate-pasting and its identity normalization;
blueprint compactification-independence step
(blueprint: lem-cbc-completed-refinement-map-functoriality).
Proof: write each refinement map as proper pushforward of the proper/open mate for
its square with left vertical identity, preceded by the inverse direct-image unit.
For two successive refinements, apply vertical proper/open mate-pasting to these
squares. The normalized clopen projector for the outer square is their pasted
projector: on the source open it is identity, and on the complementary components
it is zero. The open-unit characterization identifies the Cartesian comparison
in that projector with the specified beta. The mate equation, followed by the
canonical proper direct-image compositor, gives the map for the composite
refinement. Naturality moves the intermediate proper compositor past the mate;
its associativity cancels the inserted inverse units and yields exactly the
ordered product below. With an identity refinement, both projector and square
comparison are the identity; the two adjunction triangle equations and the
proper identity comparison leave the identity on Rp_*j_!K. To justify the alpha
equation for the actual completed coefficient sheaves, first
make this restriction calculation on module sheaves: the open/closed sequence
detects equality of maps into open extension, since the complementary restriction
vanishes. Apply the canonical module transformations on complexes and derive the
proper direct images using comparison resolutions. The defining mate equation and
the canonical derived compositors preserve this equation; this is the same
resolution comparison used in Stacks 0F7C. Thus detection is used only on sheaves,
never on derived maps or on evaluations of a derived tower. The open coefficient
identifications are the section-normalized ones in cbcDerivedOpenAdjunction.
No finite-origin or completeness hypothesis is used for these identities of maps,
as opposed to their invertibility.
The zero object, empty open, and identity refinement use the same formulas. -/
theorem cbcRefinementMap_functoriality
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (K : d.derived X) :
    (∀ c : Compactification f,
      cbcRefinementMap d (Compactification.Refinement.id c) K = 𝟙 _) ∧
    (∀ (c₁ c₂ c₃ : Compactification f) (u : c₁.Refinement c₂) (v : c₂.Refinement c₃),
      cbcRefinementMap d (u.comp v) K =
        cbcRefinementMap d v K ≫ cbcRefinementMap d u K) := by
  constructor
  · exact cbcRefinementMap_identity_component d K
  · exact cbcRefinementMap_composition_component d K

private theorem cbcCommonComparison_precomp
    {C D : Type*} [Category C] [Category D]
    (R : C → D) (m : ∀ {i j : C}, (i ⟶ j) → (R j ⟶ R i))
    (hm : ∀ {i j k : C} (f : i ⟶ j) (g : j ⟶ k), m (f ≫ g) = m g ≫ m f)
    (hi : ∀ {i j : C} (f : i ⟶ j), IsIso (m f))
    {c₀ c₁ c₂ c : C} (u₁ : c₀ ⟶ c₁) (u₂ : c₀ ⟶ c₂) (v : c ⟶ c₀) :
    @asIso _ _ _ _ (m (v ≫ u₁)) (hi _) ≪≫
        (@asIso _ _ _ _ (m (v ≫ u₂)) (hi _)).symm =
      @asIso _ _ _ _ (m u₁) (hi _) ≪≫ (@asIso _ _ _ _ (m u₂) (hi _)).symm := by
  let := hi u₁
  let := hi u₂
  let := hi v
  apply Iso.ext
  dsimp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [hm, IsIso.inv_comp, Category.assoc, IsIso.hom_inv_id_assoc]

private theorem cbcCommonComparison_independent
    {C D : Type*} [Category C] [Category D] [IsCofilteredOrEmpty C]
    (R : C → D) (m : ∀ {i j : C}, (i ⟶ j) → (R j ⟶ R i))
    (hm : ∀ {i j k : C} (f : i ⟶ j) (g : j ⟶ k), m (f ≫ g) = m g ≫ m f)
    (hi : ∀ {i j : C} (f : i ⟶ j), IsIso (m f))
    {c₀ c₀' c₁ c₂ : C} (u₁ : c₀ ⟶ c₁) (u₂ : c₀ ⟶ c₂)
    (v₁ : c₀' ⟶ c₁) (v₂ : c₀' ⟶ c₂) :
    @asIso _ _ _ _ (m u₁) (hi _) ≪≫ (@asIso _ _ _ _ (m u₂) (hi _)).symm =
      @asIso _ _ _ _ (m v₁) (hi _) ≪≫ (@asIso _ _ _ _ (m v₂) (hi _)).symm := by
  obtain ⟨c, p, q, h₁⟩ := IsCofiltered.cospan u₁ v₁
  obtain ⟨c', w, h₂⟩ := IsCofilteredOrEmpty.cone_maps (p ≫ u₂) (q ≫ v₂)
  have he₁ : (w ≫ p) ≫ u₁ = (w ≫ q) ≫ v₁ := by
    simpa only [Category.assoc] using congrArg (fun k ↦ w ≫ k) h₁
  have he₂ : (w ≫ p) ≫ u₂ = (w ≫ q) ≫ v₂ := by
    simpa only [Category.assoc] using h₂
  rw [← cbcCommonComparison_precomp R m hm hi u₁ u₂ (w ≫ p), he₁, he₂,
    cbcCommonComparison_precomp R m hm hi v₁ v₂ (w ≫ q)]

private theorem cbcIsoComparison_cocycle
    {C : Type*} [Category C] {W X Y Z : C}
    (u : X ≅ W) (v : Y ≅ W) (w : Z ≅ W) :
    (u ≪≫ v.symm) ≪≫ (v ≪≫ w.symm) = u ≪≫ w.symm := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

/-- Refinement maps are natural, unital and transitive. Compactification comparisons
are independent of the common refinement and its arrows, and satisfy the cocycle law.
Source: blueprint statement and proof step 8; Stacks 0F7C, 0F7D
(blueprint: thm-cbc-complete-proetale).
Proof: naturality follows from the proper/open mate and pushforward compositors.
Strict proper/open vertical composition with identity left proper arrows gives
C_vu = C_v followed by C_u, and the unit law gives C_id = 1. Apply Rlim to these actual
tower equations. For two common refinements take a common dominating refinement and
then equalize both pairs of arrows. Transitivity cancels the new invertible factors.
A common refinement of three compactifications likewise cancels the middle factors
and gives the cocycle. Nonemptiness covers the empty finite family. -/
theorem completeCompactSupportProetale_compactifications
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    (∀ (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
      (H : (cbcCompleteProperty d X r a ha).FullSubcategory) (k : K.obj ⟶ H.obj),
      (cbcSupport d c₂).map k ≫ cbcRefinementMap d u H.obj =
        cbcRefinementMap d u K.obj ≫ (cbcSupport d c₁).map k) ∧
    (∀ c : Compactification f,
      cbcRefinementMap d (Compactification.Refinement.id c) K.obj = 𝟙 _) ∧
    (∀ (c₁ c₂ c₃ : Compactification f) (u : c₁.Refinement c₂) (v : c₂.Refinement c₃),
      cbcRefinementMap d (u.comp v) K.obj =
        cbcRefinementMap d v K.obj ≫ cbcRefinementMap d u K.obj) ∧
    (∀ (c₀ c₀' c₁ c₂ : Compactification f)
      (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂)
      (v₁ : c₀'.Refinement c₁) (v₂ : c₀'.Refinement c₂),
      cbcCompactificationComparison d u₁ u₂ r a ha K origins =
        cbcCompactificationComparison d v₁ v₂ r a ha K origins) ∧
    (∀ (c₀ c₁ c₂ c₃ : Compactification f)
      (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂) (u₃ : c₀.Refinement c₃),
      cbcCompactificationComparison d u₁ u₂ r a ha K origins ≪≫
          cbcCompactificationComparison d u₂ u₃ r a ha K origins =
        cbcCompactificationComparison d u₁ u₃ r a ha K origins) := by
  have hl := cbcRefinementMap_functoriality d (f := f) K.obj
  refine ⟨?_, hl.1, hl.2, ?_, ?_⟩
  · intro c₁ c₂ u H k
    exact cbcRefinementMap_naturality d u k
  · intro c₀ c₀' c₁ c₂ u₁ u₂ v₁ v₂
    exact cbcCommonComparison_independent
      (fun c : Compactification f ↦ (cbcSupport d c).obj K.obj)
      (fun {c₁ c₂} u ↦ cbcRefinementMap d u K.obj)
      (fun {c₁ c₂ c₃} u v ↦ hl.2 c₁ c₂ c₃ u v)
      (fun {c₁ c₂} u ↦ cbcRefinementMap_isIso d u r a ha K origins) u₁ u₂ v₁ v₂
  · intro c₀ c₁ c₂ c₃ u₁ u₂ u₃
    exact cbcIsoComparison_cocycle
      (@asIso _ _ _ _ (cbcRefinementMap d u₁ K.obj)
        (cbcRefinementMap_isIso d u₁ r a ha K origins))
      (@asIso _ _ _ _ (cbcRefinementMap d u₂ K.obj)
        (cbcRefinementMap_isIso d u₂ r a ha K origins))
      (@asIso _ _ _ _ (cbcRefinementMap d u₃ K.obj)
        (cbcRefinementMap_isIso d u₃ r a ha K origins))

/-- The completed exchange commutes with the specified refinement maps.
Thus its compactification comparisons are comparisons of the actual exchange, not
merely isomorphisms between its endpoints.
Source: blueprint statement and proof step 8, C'_u e^c2 = e^c1 G_g C_u
(blueprint: thm-cbc-complete-proetale).
Proof: restrict to constant coefficients and identify the ordered exchange with the
strict-tower proper mate followed by beta. The strict proper/open base-change interchange
moves gamma past these two factors. Proper mate-pasting then combines the proper factors.
This is an equality of strict derived tower maps before evaluation. Apply Rlim and the
unit-normalized coefficient, open and direct-image comparisons; their conjugates give
exactly the two paths displayed below. -/
theorem completeCompactSupportProetale_refinement
    {X X' Y Y' : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
    (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
    (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g g)
    (sj₁ : OpenImmersionSquare g' c₁'.i c₁.i gb₁)
    (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g g)
    (sj₂ : OpenImmersionSquare g' c₂'.i c₂.i gb₂)
    (u : c₁.Refinement c₂) (u' : c₁'.Refinement c₂')
    (_hu : u'.hom ≫ gb₂ = gb₁ ≫ u.hom)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    (d.completedPull g).map (cbcRefinementMap d u K.obj) ≫
        cbcExchange d c₁ c₁' gb₁ sp₁ sj₁ r a ha K =
      cbcExchange d c₂ c₂' gb₂ sp₂ sj₂ r a ha K ≫
        cbcRefinementMap d (qf := cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁)
          u' ((d.completedPull g').obj K.obj) := by
  sorry

/-- Vertical pasting for supplied compatible compactification towers, with their
proper/open composition maps. Both composition maps are invertible on these inputs.
The intermediate compact-support image is complete, rather than an extra hypothesis.
Source: blueprint statement and proof step 8; Stacks 0F7F, 07A7
(blueprint: thm-cbc-complete-proetale).
Proof: in the strict quotient-tower category combine the two open comparisons into
the comparison for their composite. The proper/open interchange moves the proper mate
past gamma, and proper mate-pasting combines the remaining proper exchanges. This is
exactly the exchange for the composite compactification. Gamma is invertible on the
retained finite-origin reductions; levelwise acyclicity and Rlim give invertibility of
the specified composition maps. Open extension preserves completeness and origins,
and proper direct image preserves completeness and the individual lower bounds.
Thus the second completed exchange is defined on Rf_!K. Apply Rlim to the strict
equality and cancel the specified comparisons to obtain the two paths below. -/
theorem completeCompactSupportProetale_vertical
    {X X' Y Y' Z Z' : Scheme.{t}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
    {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (cf : Compactification f) (ch : Compactification h)
    (chf : Compactification (f ≫ h))
    (cf' : Compactification f') (ch' : Compactification h')
    (chf' : Compactification (f' ≫ h'))
    (gbf : cf'.Z ⟶ cf.Z) (gbh : ch'.Z ⟶ ch.Z) (gbhf : chf'.Z ⟶ chf.Z)
    (spf : ChosenCartesianSquare gbf cf'.g cf.g gy)
    (sjf : OpenImmersionSquare gx cf'.i cf.i gbf)
    (sph : ChosenCartesianSquare gbh ch'.g ch.g gz)
    (sjh : OpenImmersionSquare gy ch'.i ch.i gbh)
    (sphf : ChosenCartesianSquare gbhf chf'.g chf.g gz)
    (sjhf : OpenImmersionSquare gx chf'.i chf.i gbhf)
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
    (b' : cf'.Z ⟶ chf'.Z) (p' : chf'.Z ⟶ ch'.Z)
    [IsProper p]
    [IsProper p']
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g)
    (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
    (hq' : p' ≫ ch'.g = chf'.g)
    (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
    (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    IsIso (cbcTowerCompositionMap d cf ch chf b p hb hp hq sq K.obj) ∧
    IsIso (cbcTowerCompositionMap d
      (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
      cf' ch' chf' b' p' hb' hp' hq' sq' ((d.completedPull gx).obj K.obj)) ∧
    ∃ hF : cbcCompleteProperty d Y r a ha ((cbcSupport d cf).obj K.obj),
      (d.completedPull gz).map (cbcTowerCompositionMap d cf ch chf b p hb hp hq sq K.obj) ≫
          cbcExchange d chf chf' gbhf sphf sjhf r a ha K =
        cbcExchange d ch ch' gbh sph sjh r a ha ⟨(cbcSupport d cf).obj K.obj, hF⟩ ≫
          (cbcSupport d ch').map (cbcExchange d cf cf' gbf spf sjf r a ha K) ≫
          cbcTowerCompositionMap d
            (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
            cf' ch' chf' b' p' hb' hp' hq' sq' ((d.completedPull gx).obj K.obj) := by
  sorry

/-- Composition comparisons are unchanged by refinements of compatible towers.
Together with refinement cofilteredness and the preceding cocycle law this removes
all choices of tower from the vertical pasting identification.
Source: blueprint statement and proof step 8, C_hf D_2 = D_1 (C_h F_f1) (F_h2 C_f)
(blueprint: thm-cbc-complete-proetale).
Proof: let B be the proper/open square between the two intermediate open parts,
H and J the source and base refinement squares, and F the total refinement square.
Strict proper/open vertical composition on B above Q_2 and on Q_1 above J identifies
their common outer gamma. Horizontal composition on H followed by B identifies gamma_F.
Whisker by the final proper direct image and the source open extension; naturality
moves gamma_Q2 past gamma_H. Proper composition gives precisely this displayed equality
in the strict derived tower category. Applying Rlim preserves the equality. A common
refining compatible tower and the refinement cocycle then remove the chosen tower. -/
theorem completeCompactSupportProetale_composition_refinement
    {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (cf₁ cf₂ : Compactification f) (ch₁ ch₂ : Compactification h)
    (chf₁ chf₂ : Compactification (f ≫ h))
    (b₁ : cf₁.Z ⟶ chf₁.Z) (p₁ : chf₁.Z ⟶ ch₁.Z)
    (b₂ : cf₂.Z ⟶ chf₂.Z) (p₂ : chf₂.Z ⟶ ch₂.Z)
    [IsProper p₁]
    [IsProper p₂]
    (hb₁ : cf₁.i ≫ b₁ = chf₁.i) (hp₁ : b₁ ≫ p₁ = cf₁.g ≫ ch₁.i)
    (hq₁ : p₁ ≫ ch₁.g = chf₁.g)
    (hb₂ : cf₂.i ≫ b₂ = chf₂.i) (hp₂ : b₂ ≫ p₂ = cf₂.g ≫ ch₂.i)
    (hq₂ : p₂ ≫ ch₂.g = chf₂.g)
    (sq₁ : IsPullback b₁ cf₁.g p₁ ch₁.i) (sq₂ : IsPullback b₂ cf₂.g p₂ ch₂.i)
    (uf : cf₁.Refinement cf₂) (uh : ch₁.Refinement ch₂) (uhf : chf₁.Refinement chf₂)
    (_wb : uf.hom ≫ b₂ = b₁ ≫ uhf.hom) (_wp : uhf.hom ≫ p₂ = p₁ ≫ uh.hom)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    cbcTowerCompositionMap d cf₂ ch₂ chf₂ b₂ p₂ hb₂ hp₂ hq₂ sq₂ K.obj ≫
        cbcRefinementMap d uhf K.obj =
      (cbcSupport d ch₂).map (cbcRefinementMap d uf K.obj) ≫
        cbcRefinementMap d uh ((cbcSupport d cf₁).obj K.obj) ≫
          cbcTowerCompositionMap d cf₁ ch₁ chf₁ b₁ p₁ hb₁ hp₁ hq₁ sq₁ K.obj := by
  sorry

end AlgebraicGeometry.Scheme
