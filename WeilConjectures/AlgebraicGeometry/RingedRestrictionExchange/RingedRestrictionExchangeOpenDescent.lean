/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedExchangeChainUnit
public import WeilConjectures.CategoryTheory.Derived.DerivedDegreeZeroExchangeEquation
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedUpperOpenPullbackKInjective
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.OpenCube.RingedRestrictionOpenCube

public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedOpenSquareUnitNormalization
import WeilConjectures.AlgebraicGeometry.StrictTowerRingedSquare.ProEtaleRingedSquareLocalization
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedRestrictionDerivedCube
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedOrdinaryOpenExchange
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Normalized ringed restriction exchange and open descent

Source: Stacks Project, Tags 08FI, 09T5, 09A5 and 00XZ
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).

## Main statements

* `resolution_formula`: the two-resolution formula and its choice independence.
* `transpose_normalization`: the ordinary-derived adjunction normalization.
* `degreeZero_normalization`: comparison with the ordinary module exchange.
* `open_comparison`, `open_sectionwise`, `open_representative`: normalized open comparison.
* `openCube_exists`, `open_restriction`, `open_descent`: open restriction and cover detection.
* `identity_normalization`: identity base change.

`actualSquare p h R` has exactly the four rings in the statement. The general
`StrictTowerRingedSquare` interfaces allow their canonically isomorphic presentations;
no arbitrary exchange transformation is an input. Every pullback here is exact.
The tensor presentation in the published module pullback is extension only along an
isomorphism: its contraction is s ⊗ m ↦ c⁻¹(s)m, so it is precisely inverse image
with transported action. No coefficient extension or finiteness condition is imposed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u
open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 30000]
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

-- Compute first on the homotopy category, then transport through quotientCompQhIso.
section DerivedTranspose
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private theorem transpose_homotopy (adj : L ⊣ R)
    (A : HomotopyCategory C (.up ℤ)) (B : HomotopyCategory D (.up ℤ))
    (k : (L.mapHomotopyCategory (.up ℤ)).obj A ⟶ B) :
    adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv
        (DerivedCategory.Qh.obj A) (DerivedCategory.Qh.obj B)
        (L.mapDerivedCategoryFactorsh.hom.app A ≫ DerivedCategory.Qh.map k) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).homEquiv A B k) ≫
        R.rightDerivedFunctorUnit.app B := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc]
  change (((adj.mapHomotopyCategory (.up ℤ)).derivedη
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit).app _ ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app A)) ≫ _ = _
  rw [Adjunction.derivedη_fac_app, Category.assoc]
  have hn := R.rightDerivedFunctorUnit.naturality k
  dsimp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc]

private theorem transpose_complex (adj : L ⊣ R)
    (A : CochainComplex C ℤ) (B : CochainComplex D ℤ) [B.IsKInjective]
    (k : (L.mapHomologicalComplex (.up ℤ)).obj A ⟶ B) :
    adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv
        (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (L.mapDerivedCategoryFactors.hom.app A ≫ DerivedCategory.Q.map k) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv A B k) ≫
        (R.rightDerivedFunctorObjQIso B).inv := by
  let qC := HomotopyCategory.quotient C (.up ℤ)
  let qD := HomotopyCategory.quotient D (.up ℤ)
  let eC := (DerivedCategory.quotientCompQhIso C).app A
  let eD := (DerivedCategory.quotientCompQhIso D).app B
  have hleft : L.mapDerivedCategory.map eC.hom ≫
        L.mapDerivedCategoryFactors.hom.app A ≫ DerivedCategory.Q.map k =
      L.mapDerivedCategoryFactorsh.hom.app (qC.obj A) ≫
        DerivedCategory.Qh.map (qD.map k) ≫ eD.hom := by
    have hfac : DerivedCategory.Qh.map
        ((L.mapHomotopyCategoryFactors (.up ℤ)).inv.app A) = 𝟙 _ := by
      change DerivedCategory.Qh.map (𝟙 _) = _
      exact DerivedCategory.Qh.map_id _
    rw [Functor.mapDerivedCategoryFactorsh_hom_app, hfac]
    erw [Category.comp_id]
    have hc : eC.hom = 𝟙 _ := rfl
    have hd : eD.hom = 𝟙 _ := rfl
    have hi : (DerivedCategory.quotientCompQhIso D).inv.app
        ((L.mapHomologicalComplex (.up ℤ)).obj A) = 𝟙 _ := rfl
    rw [hc, hd, hi]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp,
      Category.comp_id, Category.comp_id]
    rfl
  rw [← cancel_epi eC.hom,
    ← adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv_naturality_left,
    hleft, ← Category.assoc,
    adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv_naturality_right]
  erw [transpose_homotopy]
  have ht : (adj.mapHomotopyCategory (.up ℤ)).homEquiv (qC.obj A) (qD.obj B)
        (qD.map k) = qC.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv A B k) := by
    dsimp only [qC, qD]
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      Adjunction.mapHomotopyCategory_unit_app_quotient, Functor.mapHomotopyCategory_map,
      CategoryTheory.Functor.map_comp]
  rw [ht]
  dsimp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, asIso_hom]
  simp only [Category.assoc]
  have hc : eC.hom = 𝟙 _ := rfl
  have hd : eD.hom = 𝟙 _ := rfl
  have hi : (DerivedCategory.quotientCompQhIso C).inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj B) = 𝟙 _ := rfl
  rw [hc, hd, hi]
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  rfl
end DerivedTranspose

namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingModuleAdjunction proEtaleCanonicalDerivedPullbackComparison
  StrictTowerRingedSquare.exchangeModuleSquare

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

/-- Exact localization of the canonical inverse-image square. Source: Stacks 09T5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
abbrev pullSquare (r : StrictTowerRingedSquare sq) :
    (basePull r).mapDerivedCategory ⋙ (targetPull r).mapDerivedCategory ≅
      (verticalPull r).mapDerivedCategory ⋙ (upperPull r).mapDerivedCategory :=
  proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
    r.cf r.cg r.cg' r.cf' r.coherent

/-- The canonical quasi-isomorphism-independent resolution comparison; it does not require
that the resolution map be monic. Source: Stacks 070I and 070K
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def resolutionIso (r : StrictTowerRingedSquare sq)
    {K I : CochainComplex (proEtaleRingModules X r.RX) ℤ}
    [I.IsKInjective] (a : K ⟶ I) [QuasiIso a] :
    (verticalPush r).rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((verticalPush r).mapHomologicalComplex (.up ℤ)).obj I) :=
  (verticalPush r).rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map a)) ≪≫
    (verticalPush r).rightDerivedFunctorObjQIso I

private def ringCompAt {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    proEtaleSheafInverseImage fg CommRingCat.{u + 1} ≅
      proEtaleSheafInverseImage g CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage f CommRingCat.{u + 1} :=
  ((conjugateIsoEquiv (proEtaleSheafAdjunction fg CommRingCat.{u + 1})
    ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction f CommRingCat.{u + 1}))).symm
    (Functor.sheafPushforwardContinuousComp'
      (eFG := (MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g fg hfg).symm) CommRingCat.{u + 1}
      (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).symm).symm

private theorem ringCompAt_left {P T : Scheme.{u}} (p : P ⟶ T) :
    ringCompAt (𝟙 P) p p (Category.id_comp p).symm =
      (proEtaleSheafInverseImage p CommRingCat.{u + 1}).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (proEtaleSheafInverseImage p CommRingCat.{u + 1})
          (proEtaleRingInverseImageId P).symm := by
  let a := proEtaleSheafAdjunction p CommRingCat.{u + 1}
  let b := proEtaleSheafAdjunction (𝟙 P) CommRingCat.{u + 1}
  apply (conjugateIsoEquiv (a.comp b) a).injective
  rw [show conjugateIsoEquiv (a.comp b) a
      (ringCompAt (𝟙 P) p p (Category.id_comp p).symm) =
      Functor.sheafPushforwardContinuousComp'
        (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          (𝟙 P) p p (Category.id_comp p).symm).symm) CommRingCat.{u + 1}
          (ProEt.topology T) (ProEt.topology P) (ProEt.topology P) from
    (conjugateIsoEquiv_iso_symm a (a.comp b) _).trans
      (congrArg Iso.symm ((conjugateIsoEquiv a (a.comp b)).apply_symm_apply _))]
  rw [conjugateIsoEquiv_trans _ (a.comp Adjunction.id) _]
  simp only [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_rightUnitor]
  have hid : conjugateIsoEquiv Adjunction.id b (proEtaleRingInverseImageId P) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} P).symm :=
    Equiv.apply_symm_apply _ _
  rw [hid]
  ext M V
  simp only [Functor.sheafPushforwardContinuousComp',
    MorphismProperty.Over.pullbackComp_id_left p p (Category.id_comp p).symm]
  simp
  rfl

private theorem ringCompAt_right {P T : Scheme.{u}} (p : P ⟶ T) :
    ringCompAt p (𝟙 T) p (Category.comp_id p).symm =
      (proEtaleSheafInverseImage p CommRingCat.{u + 1}).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (proEtaleRingInverseImageId T).symm
          (proEtaleSheafInverseImage p CommRingCat.{u + 1}) := by
  let a := proEtaleSheafAdjunction p CommRingCat.{u + 1}
  let b := proEtaleSheafAdjunction (𝟙 T) CommRingCat.{u + 1}
  apply (conjugateIsoEquiv (b.comp a) a).injective
  rw [show conjugateIsoEquiv (b.comp a) a
      (ringCompAt p (𝟙 T) p (Category.comp_id p).symm) =
      Functor.sheafPushforwardContinuousComp'
        (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          p (𝟙 T) p (Category.comp_id p).symm).symm) CommRingCat.{u + 1}
          (ProEt.topology T) (ProEt.topology T) (ProEt.topology P) from
    (conjugateIsoEquiv_iso_symm a (b.comp a) _).trans
      (congrArg Iso.symm ((conjugateIsoEquiv a (b.comp a)).apply_symm_apply _))]
  rw [conjugateIsoEquiv_trans _ (Adjunction.id.comp a) _]
  simp only [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_leftUnitor]
  have hid : conjugateIsoEquiv Adjunction.id b (proEtaleRingInverseImageId T) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} T).symm :=
    Equiv.apply_symm_apply _ _
  rw [hid]
  ext M V
  simp only [Functor.sheafPushforwardContinuousComp',
    MorphismProperty.Over.pullbackComp_id_right p p (Category.comp_id p).symm]
  simp
  rfl
private theorem ringComposite_heq {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) (q : Z ⟶ V) (hq : q = h ≫ k)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ) :
    HEq (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)
      ((ringCompAt h k q hq).app RV ≪≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso ck ≪≫ ch) := by
  subst q
  rfl



section Comparisons
universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive]

/-- The canonical δ on modules in degree zero, retaining the single-complex comparison.
Source: Stacks 070K (blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def degreeZeroComparison [Abelian.HasKInjectiveResolutions C] (M : C) :
    DerivedCategory.Q.obj ((HomologicalComplex.single D (.up ℤ) 0).obj (F.obj M)) ⟶
      F.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj M)) :=
  DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
    chainComparison F ((HomologicalComplex.single C (.up ℤ) 0).obj M)

/-- Exact inverse image commutes canonically with the degree-zero embedding.
Source: Stacks 09T5 (blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def degreeZeroPullIso [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : C) :
    F.mapDerivedCategory.obj
        (DerivedCategory.Q.obj ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single D (.up ℤ) 0).obj (F.obj M)) :=
  F.mapDerivedCategoryFactors.app ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M)
end Comparisons

private theorem chainComparison_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} (a : K ⟶ L) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) ≫
        chainComparison F L =
      chainComparison F K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map a) := by
  exact F.rightDerivedFunctorUnitQ_naturality a

private theorem chainComparison_isKInjective
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) [I.IsKInjective] :
    chainComparison F I = (F.rightDerivedFunctorObjQIso I).inv := by
  exact F.rightDerivedFunctorUnitQ_eq I

private theorem exchange_chain (r : StrictTowerRingedSquare sq)
    (K : CochainComplex (proEtaleRingModules X r.RX) ℤ) :
    (basePull r).mapDerivedCategory.map (chainComparison (verticalPush r) K) ≫
        (exchange r).app (DerivedCategory.Q.obj K) ≫
        (targetPush r).rightDerivedFunctor.map
          ((upperPull r).mapDerivedCategoryFactors.hom.app K) =
      (basePull r).mapDerivedCategoryFactors.hom.app
          (((verticalPush r).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinary r) (.up ℤ)).app K) ≫
        chainComparison (targetPush r)
          (((upperPull r).mapHomologicalComplex (.up ℤ)).obj K) := by
  exact exchange_chainUnit r K

attribute [local irreducible] ordinary proEtaleAmbientRingedExchange

private theorem resolution_comparison
    {C : Type*} [Category C] {A B D E F G H I : C}
    (e : A ≅ B) (j : H ≅ I) (x : A ⟶ F) (t : F ⟶ G)
    (v : B ⟶ D) (w : D ⟶ E) (δ : E ⟶ G) (b : E ⟶ I) (d : G ⟶ H)
    (h : e.inv ≫ x ≫ t = v ≫ w ≫ δ) (hb : b ≫ j.inv = δ ≫ d) :
    e.hom ≫ v ≫ w ≫ b = x ≫ t ≫ d ≫ j.hom := by
  apply (cancel_mono j.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hb, ← reassoc_of% h, Iso.hom_inv_id_assoc]

/-- The normalized exchange is computed by every pair of K-injective resolutions.
Source: Stacks 070I, 070K and 09T5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: steps 2--4 of the node. Exact inverse image and its module adjunction imply that
direct image preserves K-injectives. The derived Hom bijection into a K-injective
complex is the ordinary Hom bijection on chain maps modulo homotopy. Transposing the
canonical square followed by the counit and b therefore gives p'_*b after bc_I.
Naturality gives the same formula for derived morphisms. For two resolutions the
K-injective comparison principle supplies homotopy equivalences t and s satisfying
sb = b' h'⁻¹t up to homotopy. Ordinary exchange naturality identifies the two formulas
under the resulting canonical derived comparisons. The displayed equation holds for
all a and b, so includes precisely this independence, without requiring h'⁻¹I to be
K-injective. -/
theorem resolution_formula (r : StrictTowerRingedSquare sq)
    {K I : CochainComplex (proEtaleRingModules X r.RX) ℤ}
    [I.IsKInjective] (a : K ⟶ I) [QuasiIso a]
    {J : CochainComplex (proEtaleRingModules X' r.RX') ℤ} [J.IsKInjective]
    (b : ((upperPull r).mapHomologicalComplex (.up ℤ)).obj I ⟶ J) [QuasiIso b] :
    (basePull r).mapDerivedCategory.map (resolutionIso r a).hom ≫
        (basePull r).mapDerivedCategoryFactors.hom.app
          (((verticalPush r).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinary r) (.up ℤ)).app I ≫
            ((targetPush r).mapHomologicalComplex (.up ℤ)).map b) =
      (exchange r).app (DerivedCategory.Q.obj K) ≫
        (targetPush r).rightDerivedFunctor.map
          ((upperPull r).mapDerivedCategoryFactors.hom.app K ≫
            DerivedCategory.Q.map (((upperPull r).mapHomologicalComplex (.up ℤ)).map a) ≫
            DerivedCategory.Q.map b) ≫
        ((targetPush r).rightDerivedFunctorObjQIso J).hom := by
  have h := exchange_chain r I
  rw [chainComparison_isKInjective] at h
  have hn := chainComparison_naturality (targetPush r) b
  rw [chainComparison_isKInjective] at hn
  have hi := resolution_comparison
    ((basePull r).mapDerivedCategory.mapIso
      ((verticalPush r).rightDerivedFunctorObjQIso I))
    ((targetPush r).rightDerivedFunctorObjQIso J)
    ((exchange r).app (DerivedCategory.Q.obj I))
    ((targetPush r).rightDerivedFunctor.map
      ((upperPull r).mapDerivedCategoryFactors.hom.app I))
    ((basePull r).mapDerivedCategoryFactors.hom.app
      (((verticalPush r).mapHomologicalComplex (.up ℤ)).obj I))
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinary r) (.up ℤ)).app I))
    (chainComparison (targetPush r) (((upperPull r).mapHomologicalComplex (.up ℤ)).obj I))
    (DerivedCategory.Q.map (((targetPush r).mapHomologicalComplex (.up ℤ)).map b))
    ((targetPush r).rightDerivedFunctor.map (DerivedCategory.Q.map b)) h hn
  dsimp only [resolutionIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  erw [hi]
  have hn := (exchange r).naturality (DerivedCategory.Q.map a)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp_assoc,
    (upperPull r).mapDerivedCategoryFactors_hom_naturality]
  simp only [Functor.map_comp, Category.assoc]

/-- The derived adjunction has the chain-map transpose normalization of the node.
Source: Stacks 09T5 and 070I
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 2. Direct image preserves K-injectives because its left adjoint is exact.
The two derived Hom sets into I and its direct image are the corresponding homotopy
Hom sets by kinjective-hom-derived. Between them the derived adjunction is precisely
the ordinary degreewise adjunction. Its chain-map transpose therefore represents the
derived transpose; the right-derived object comparison is the inverse derived unit. -/
theorem transpose_normalization (r : StrictTowerRingedSquare sq)
    (L : CochainComplex (proEtaleRingModules Y r.RY) ℤ)
    (I : CochainComplex (proEtaleRingModules X r.RX) ℤ) [I.IsKInjective]
    (k : ((verticalPull r).mapHomologicalComplex (.up ℤ)).obj L ⟶ I) :
    (proEtaleRingDerivedAdjunction f r.RY r.RX r.cf).homEquiv
        (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)
        ((verticalPull r).mapDerivedCategoryFactors.hom.app L ≫ DerivedCategory.Q.map k) =
      DerivedCategory.Q.map
          (((proEtaleRingModuleAdjunction f r.RY r.RX r.cf).mapHomologicalComplex
            (.up ℤ)).homEquiv L I k) ≫
        ((verticalPush r).rightDerivedFunctorObjQIso I).inv := by
  exact transpose_complex (proEtaleRingModuleAdjunction f r.RY r.RX r.cf) L I k

section SingleComparison
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]

private theorem single_exchange (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (J : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    (e : F ⋙ G ⟶ H ⋙ J) (M : A) :
    (G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) ≫
      (NatTrans.mapHomologicalComplex e (.up ℤ)).app
        ((HomologicalComplex.single A (.up ℤ) 0).obj M) ≫
      (J.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app M) =
    (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M) ≫
      (HomologicalComplex.single D (.up ℤ) 0).map (e.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).inv.app (H.obj M) := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self]
    dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
    change G.map (𝟙 (F.obj M) ≫ F.map (𝟙 M)) ≫ e.app M ≫
        J.map (H.map (𝟙 M) ≫ 𝟙 _) =
      (G.map (𝟙 (F.obj M)) ≫ 𝟙 _) ≫ (𝟙 _ ≫ e.app M ≫ 𝟙 _) ≫ 𝟙 _ ≫ J.map (𝟙 _)
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_ne _ _ hn,
      Functor.map_zero, comp_zero, zero_comp]

private theorem degreeZero_of_chain
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions A]
    [Abelian.HasKInjectiveResolutions C]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (J : C ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] [J.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ⟶ H ⋙ J)
    (δ : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ J.rightDerivedFunctor)
    (hδ : ∀ K : CochainComplex A ℤ,
      G.mapDerivedCategory.map (chainComparison F K) ≫
          δ.app (DerivedCategory.Q.obj K) ≫
          J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app K) =
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app K) ≫
          chainComparison J ((H.mapHomologicalComplex (.up ℤ)).obj K)) (M : A) :
    G.mapDerivedCategory.map (degreeZeroComparison F M) ≫
        δ.app (DerivedCategory.Q.obj ((HomologicalComplex.single A (.up ℤ) 0).obj M)) ≫
        J.rightDerivedFunctor.map (degreeZeroPullIso H M).hom =
      (degreeZeroPullIso G (F.obj M)).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single D (.up ℤ) 0).map (e.app M)) ≫
        degreeZeroComparison J (H.obj M) := by
  let K := (HomologicalComplex.single A (.up ℤ) 0).obj M
  let a := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app M
  let b := (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app M
  have hs := single_exchange F G H J e M
  have hn := chainComparison_naturality J b
  dsimp only [degreeZeroComparison, degreeZeroPullIso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hδ K]
  erw [← hn]
  erw [G.mapDerivedCategoryFactors_hom_naturality_assoc a]
  simp only [← Functor.map_comp_assoc]
  rw [hs]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end SingleComparison

-- Keep the native module-category instances while the four functors are variables.
section SchemeSingleComparison
variable (r : StrictTowerRingedSquare sq)
  (F : proEtaleRingModules X r.RX ⥤ proEtaleRingModules Y r.RY)
  (G : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules Y' r.RY')
  (H : proEtaleRingModules X r.RX ⥤ proEtaleRingModules X' r.RX')
  (J : proEtaleRingModules X' r.RX' ⥤ proEtaleRingModules Y' r.RY')
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private theorem scheme_degreeZero_of_chain
    (e : F ⋙ G ⟶ H ⋙ J)
    (δ : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ J.rightDerivedFunctor)
    (hδ : ∀ K : CochainComplex (proEtaleRingModules X r.RX) ℤ,
      G.mapDerivedCategory.map (chainComparison F K) ≫
          δ.app (DerivedCategory.Q.obj K) ≫
          J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app K) =
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app K) ≫
          chainComparison J ((H.mapHomologicalComplex (.up ℤ)).obj K))
    (M : proEtaleRingModules X r.RX) :
    DerivedDegreeZeroExchangeEquation F G H J e δ
      (degreeZeroComparison F) (degreeZeroComparison J)
      (degreeZeroPullIso G) (degreeZeroPullIso H) M := by
  exact degreeZero_of_chain F G H J e δ hδ M
end SchemeSingleComparison

section DegreeZeroNormalization

/-- The degree-zero normalization Ex ∘ h⁻¹δ = δ ∘ bc[0], with every single-complex
identification explicit. Source: Stacks 070K and 09T5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 5. Specialize exchange_chainUnit to M[0]. Naturality of the target
cochain comparison moves the upper single-complex comparison past that unit.
Naturality of the base localization comparison moves the source single-complex
comparison to the ordinary side. Degreewise, the resulting three-map composite
is the single-complex map of ordinary exchange: degree zero uses functoriality
of identities, and every other degree uses the zero target comparison.
Functoriality of Q and associativity give the displayed equality. -/
theorem degreeZero_normalization (r : StrictTowerRingedSquare sq)
    (M : proEtaleRingModules X r.RX) :
    DerivedDegreeZeroExchangeEquation (verticalPush r) (basePull r)
      (upperPull r) (targetPush r) (ordinary r) (exchange r)
      (degreeZeroComparison (verticalPush r)) (degreeZeroComparison (targetPush r))
      (degreeZeroPullIso (basePull r)) (degreeZeroPullIso (upperPull r)) M := by
  exact scheme_degreeZero_of_chain r (verticalPush r) (basePull r)
    (upperPull r) (targetPush r) (ordinary r) (exchange r) (exchange_chainUnit r) M
end DegreeZeroNormalization



attribute [local semireducible] proEtaleRingModuleDirectImage

/-- Restriction to an open preserves K-injective complexes, including transported
inverse-image rings. Source: Stacks 08FI and 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 6. The ringed open comparison identifies this inverse image with slice
restriction. Exact extension by zero is its left adjoint, so localized restriction
preserves K-injectives by kinjective-restrict-localized-universes. Coefficient and
site equivalences preserve the same Hom-vanishing condition. -/
theorem open_inverseImage_isKInjective {S Z : Scheme.{u}} (j : S ⟶ Z)
    [IsOpenImmersion j] (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (R' : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R ≅ R')
    (I : CochainComplex (proEtaleRingModules Z R) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((proEtaleRingModulePullback j R R' c).mapHomologicalComplex (.up ℤ)).obj I) := by
  infer_instance

/-- The upper open restriction also preserves K-injectives. Source: Stacks 08FI
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: the Cartesian identification makes g' a base change of the open g. It is
therefore open. Apply open_inverseImage_isKInjective with its specified coefficients;
this is step 6 applied to the upper base change. -/
theorem open_upper_isKInjective (r : StrictTowerRingedSquare sq)
    [IsOpenImmersion g] (I : CochainComplex (proEtaleRingModules X r.RX) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective (((upperPull r).mapHomologicalComplex (.up ℤ)).obj I) := by
  have : IsOpenImmersion g' := by
    rw [← sq.hom_fst]
    infer_instance
  exact open_inverseImage_isKInjective g' r.RX r.RX' r.cg' I

section OpenComparisonTransfer
attribute [local irreducible] proEtaleRingModuleDirectImage
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (J : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesKInjectiveComplexes]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derived_iso_of_chain (e : F ⋙ G ⟶ H ⋙ J) [IsIso e]
    (δ : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ J.rightDerivedFunctor)
    (hδ : ∀ I : CochainComplex A ℤ,
      G.mapDerivedCategory.map (chainComparison F I) ≫
          δ.app (DerivedCategory.Q.obj I) ≫
          J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app I) ≫
          chainComparison J ((H.mapHomologicalComplex (.up ℤ)).obj I)) :
    IsIso δ := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  let L := DerivedCategory.Q.objPreimage K
  obtain ⟨I, hI, a, ha, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective L
  have hQI : IsIso (δ.app (DerivedCategory.Q.obj I)) := by
    have h := hδ I
    rw [chainComparison_isKInjective, chainComparison_isKInjective] at h
    have hi : IsIso
        (G.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).inv ≫
          δ.app (DerivedCategory.Q.obj I) ≫
          J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) := by
      rw [h]
      exact ((G.mapDerivedCategoryFactors.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≪≫
          DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (asIso e) (.up ℤ)).app I) ≪≫
          (J.rightDerivedFunctorObjQIso
            ((H.mapHomologicalComplex (.up ℤ)).obj I)).symm).isIso_hom
    have hi' : IsIso (δ.app (DerivedCategory.Q.obj I) ≫
        J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) :=
      IsIso.of_isIso_comp_left
        (G.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).inv) _
    exact IsIso.of_isIso_comp_right _
      (J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I))
  let i : DerivedCategory.Q.obj I ≅ K :=
    (asIso (DerivedCategory.Q.map a)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K
  exact (NatTrans.isIso_app_iff_of_iso δ i).mp hQI

end OpenComparisonTransfer

-- Specialize the category instances before substituting the ringed functors.
section SchemeOpenComparisonTransfer
variable (r : StrictTowerRingedSquare sq)
  (F : proEtaleRingModules X r.RX ⥤ proEtaleRingModules Y r.RY)
  (G : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules Y' r.RY')
  (H : proEtaleRingModules X r.RX ⥤ proEtaleRingModules X' r.RX')
  (J : proEtaleRingModules X' r.RX' ⥤ proEtaleRingModules Y' r.RY')
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesKInjectiveComplexes]

private theorem scheme_derived_iso_of_chain (e : F ⋙ G ⟶ H ⋙ J) [IsIso e]
    (δ : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ J.rightDerivedFunctor)
    (hδ : ∀ I : CochainComplex (proEtaleRingModules X r.RX) ℤ,
      G.mapDerivedCategory.map (chainComparison F I) ≫
          δ.app (DerivedCategory.Q.obj I) ≫
          J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app I) ≫
          chainComparison J ((H.mapHomologicalComplex (.up ℤ)).obj I)) :
    IsIso δ := by
  exact derived_iso_of_chain F G H J e δ hδ
end SchemeOpenComparisonTransfer

/-- The open comparison is the specified derived mate and is an isomorphism.
Source: Stacks 08FI, 09A5 and 00XZ
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 6. On a K-injective I the two functors evaluate on Q → U as sections on
S ×_Z Q and S_U ×_U Q. Their canonical fibre-product identification gives the ordinary
comparison of proetale-open-restriction-counit, with the same ring action. Open restriction
preserves K-injectives, so its termwise comparison computes both derived functors.
The resolution formula identifies it with the derived mate. It is invertible and
natural, independently of I. The ordinary geometric assertion is isolated as
ordinary_open_isIso. For the derived assertion, exchange_chain on a K-injective
resolution has invertible cochain units on both sides, since upper open pullback
preserves K-injectives. The termwise ordinary exchange is invertible degreewise.
Cancel the two comparison factors, then transport along the resolution isomorphism
using naturality of exchange. -/
theorem open_comparison (r : StrictTowerRingedSquare sq) [IsOpenImmersion g] :
    IsIso (ordinary r) ∧ IsIso (exchange r) := by
  have ho : IsIso (ordinary r) := ordinary_open_isIso r
  refine ⟨ho, ?_⟩
  exact scheme_derived_iso_of_chain r (verticalPush r) (basePull r) (upperPull r) (targetPush r)
    (ordinary r) (exchange r) (exchange_chain r)

section OpenSectionwise

private theorem mate_eq_of_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L ⊣ R) (a' : L' ⊣ R')
    (θ : G ⋙ L' ≅ L ⋙ H) (β : R ⋙ G ⟶ H ⋙ R')
    (hc : ∀ M, H.map (a.counit.app M) =
      θ.inv.app (R.obj M) ≫ L'.map (β.app M) ≫ a'.counit.app (H.obj M)) :
    β = (mateEquiv a a' (TwoSquare.mk _ _ _ _ θ.hom)).natTrans := by
  apply NatTrans.ext
  funext M
  apply (a'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  apply (cancel_epi (θ.inv.app (R.obj M))).mp
  rw [← hc M, mateEquiv_counit]
  simp

private theorem open_alpha_unique {P T U : Scheme.{u}} (p : P ⟶ T) (j : U ⟶ T)
    [IsOpenImmersion j] (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α β : ProEtaleOpenRestriction.AlphaL p j R ≅
      ProEtaleOpenRestriction.AlphaR p j R (ProEtaleOpenRestriction.coefficientIso p j R))
    (hα : ProEtaleOpenRestriction.AlphaNormalization p j R α)
    (hβ : ProEtaleOpenRestriction.AlphaNormalization p j R β) : α = β := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (((ProEtaleOpenRestriction.AdjF p R).comp
    (ProEtaleOpenRestriction.AdjF (pullback.fst p j)
      (ProEtaleOpenRestriction.RX p R))).homEquiv M _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V m
  exact (hα M V.unop m).trans (hβ M V.unop m).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem native_mate_eq_of_counit {P T U : Scheme.{u}} (p : P ⟶ T) (j : U ⟶ T)
    [IsOpenImmersion j] (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (α : ProEtaleOpenRestriction.AlphaL p j R ≅
      ProEtaleOpenRestriction.AlphaR p j R (ProEtaleOpenRestriction.coefficientIso p j R))
    (β : ProEtaleOpenRestriction.Left p j R ≅
      ProEtaleOpenRestriction.Right p j R (ProEtaleOpenRestriction.coefficientIso p j R))
    (hc : ProEtaleOpenRestriction.CounitEquation p j R β α) :
    β.hom = (mateEquiv (ProEtaleOpenRestriction.AdjF p R)
      (ProEtaleOpenRestriction.AdjSnd p j R (ProEtaleOpenRestriction.coefficientIso p j R))
      (TwoSquare.mk (ProEtaleOpenRestriction.PH p j R) _ _
        (ProEtaleOpenRestriction.PFst p j R) α.inv)).natTrans := by
  exact mate_eq_of_counit (ProEtaleOpenRestriction.AdjF p R)
    (ProEtaleOpenRestriction.AdjSnd p j R (ProEtaleOpenRestriction.coefficientIso p j R))
    α.symm β.hom hc


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem native_mate_eq_ordinary {P T U : Scheme.{u}} (p : P ⟶ T) (j : U ⟶ T)
    [IsOpenImmersion j] (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    (mateEquiv (ProEtaleOpenRestriction.AdjF p R)
      (ProEtaleOpenRestriction.AdjSnd p j R (ProEtaleOpenRestriction.coefficientIso p j R))
      (TwoSquare.mk (ProEtaleOpenRestriction.PH p j R) _ _
        (ProEtaleOpenRestriction.PFst p j R)
        (actualSquare p j R).exchangeModuleSquare.hom)).natTrans =
      ordinary (actualSquare p j R) := by
  unfold ordinary actualSquare
  rfl


/-- The ordinary open comparison retains exactly its section identification, rather than
an arbitrary isomorphism. Source: Stacks 09A5 and 00XZ
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 6. The canonical open-slice coprojections identify inverse image with
restriction. The counit equation of proetale-open-restriction-counit identifies its
comparison with the ordinary mate. Evaluating that comparison on Q gives restriction
along the canonical arrow S_U ×_U Q → S ×_Z Q, with equal scalar actions. -/
theorem open_sectionwise {P T U : Scheme.{u}} (p : P ⟶ T) (j : U ⟶ T)
    [IsOpenImmersion j] (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    ∃ β : ProEtaleOpenRestriction.Left p j R ≅
        ProEtaleOpenRestriction.Right p j R (ProEtaleOpenRestriction.coefficientIso p j R),
      β.hom = ordinary (actualSquare p j R) ∧
        ProEtaleOpenRestriction.Sectionwise p j R β := by
  obtain ⟨β, hβ, α, hα, hc⟩ :=
    ProEtaleOpenRestriction.proEtaleOpenRestrictionCounit p j R
  refine ⟨β, ?_, hβ⟩
  have he := open_alpha_unique p j R α _ hα (actual_open_square_alpha_normalization p j R)
  subst α
  exact (native_mate_eq_of_counit p j R _ β hc).trans (native_mate_eq_ordinary p j R)


end OpenSectionwise

private theorem inverse_composite_eq {C : Type*} [Category C]
    {A B D E : C} (a : A ≅ B) (b : B ≅ D) (e : D ⟶ E) (t : A ⟶ E)
    (h : a.hom ≫ b.hom ≫ e = t) : b.inv ≫ a.inv ≫ t = e := by
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

/-- On every K-injective representative the derived open comparison is its prescribed
sectionwise ordinary comparison. Source: Stacks 08FI and 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 6. Apply the resolution formula with a = id and b = id. Their targets are
K-injective by open_inverseImage_isKInjective. The resulting equation is termwise
ordinary exchange on I, transported by the two canonical right-derived comparisons. -/
theorem open_representative (r : StrictTowerRingedSquare sq) [IsOpenImmersion g]
    (I : CochainComplex (proEtaleRingModules X r.RX) ℤ) [I.IsKInjective] :
    (basePull r).mapDerivedCategoryFactors.inv.app
        (((verticalPush r).mapHomologicalComplex (.up ℤ)).obj I) ≫
        (basePull r).mapDerivedCategory.map
          ((verticalPush r).rightDerivedFunctorObjQIso I).inv ≫
        (exchange r).app (DerivedCategory.Q.obj I) ≫
        (targetPush r).rightDerivedFunctor.map
          ((upperPull r).mapDerivedCategoryFactors.hom.app I) ≫
        ((targetPush r).rightDerivedFunctorObjQIso
          (((upperPull r).mapHomologicalComplex (.up ℤ)).obj I)).hom =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinary r) (.up ℤ)).app I) := by
  have h := resolution_formula r (𝟙 I)
    (𝟙 (((upperPull r).mapHomologicalComplex (.up ℤ)).obj I))
  dsimp only [resolutionIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom] at h
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact inverse_composite_eq
    ((basePull r).mapDerivedCategory.mapIso
      ((verticalPush r).rightDerivedFunctorObjQIso I))
    ((basePull r).mapDerivedCategoryFactors.app
      (((verticalPush r).mapHomologicalComplex (.up ℤ)).obj I)) _ _
    h

variable {U : Scheme.{u}} {j : U ⟶ Y}


private def directCompAt {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    proEtaleSheafDirectImage f CommRingCat.{u + 1} ⋙
        proEtaleSheafDirectImage g CommRingCat.{u + 1} ≅
      proEtaleSheafDirectImage fg CommRingCat.{u + 1} :=
  Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp
      (P := @WeaklyEtale) (Q := ⊤) f g fg hfg).symm) CommRingCat.{u + 1}
      (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)

private theorem ringCompAt_conjugate {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    conjugateIsoEquiv
      ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).comp
        (proEtaleSheafAdjunction f CommRingCat.{u + 1}))
      (proEtaleSheafAdjunction fg CommRingCat.{u + 1}) (ringCompAt f g fg hfg) =
      directCompAt f g fg hfg := by
  exact (conjugateIsoEquiv_iso_symm _ _ _).trans
    (congrArg Iso.symm ((conjugateIsoEquiv _ _).apply_symm_apply _))

private theorem directCompAt_assoc {X Y Z V : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fgh : X ⟶ V) (hfgh : fgh = f ≫ g ≫ h) :
    (proEtaleSheafDirectImage f CommRingCat.{u + 1}).associator
        (proEtaleSheafDirectImage g CommRingCat.{u + 1})
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}) ≪≫
      Functor.isoWhiskerLeft (proEtaleSheafDirectImage f CommRingCat.{u + 1})
        (directCompAt g h (g ≫ h) rfl) ≪≫ directCompAt f (g ≫ h) fgh hfgh =
    Functor.isoWhiskerRight (directCompAt f g (f ≫ g) rfl)
        (proEtaleSheafDirectImage h CommRingCat.{u + 1}) ≪≫
      directCompAt (f ≫ g) h fgh (by rw [hfgh, Category.assoc]) := by
  ext M b
  have key := congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_assoc (P := @WeaklyEtale) (Q := ⊤)
      f g h fgh hfgh)) (unop b)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at key
  simp only [directCompAt, proEtaleSheafDirectImage, AlgebraicGeometry.ProEtale.lowerStar]
  simp only [Functor.comp_obj, Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, Iso.symm_inv,
    Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op, ← Functor.map_comp,
    ← op_comp, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.sheafPushforwardContinuous_map_hom_app]
  rw [key]

private theorem ringCompAt_assoc {X Y Z V : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ V)
    (fgh : X ⟶ V) (hfgh : fgh = f ≫ g ≫ h) :
    ringCompAt f (g ≫ h) fgh hfgh ≪≫
        Functor.isoWhiskerRight (ringCompAt g h (g ≫ h) rfl)
          (proEtaleSheafInverseImage f CommRingCat.{u + 1}) ≪≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).associator
          (proEtaleSheafInverseImage g CommRingCat.{u + 1})
          (proEtaleSheafInverseImage f CommRingCat.{u + 1}) =
      ringCompAt (f ≫ g) h fgh (by rw [hfgh, Category.assoc]) ≪≫
        Functor.isoWhiskerLeft (proEtaleSheafInverseImage h CommRingCat.{u + 1})
          (ringCompAt f g (f ≫ g) rfl) := by
  refine (conjugateIsoEquiv
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
      ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).comp
        (proEtaleSheafAdjunction f CommRingCat.{u + 1})))
    (proEtaleSheafAdjunction fgh CommRingCat.{u + 1})).injective ?_
  rw [conjugateIsoEquiv_trans _
      ((proEtaleSheafAdjunction (g ≫ h) CommRingCat.{u + 1}).comp
        (proEtaleSheafAdjunction f CommRingCat.{u + 1})) _,
    conjugateIsoEquiv_trans _
      (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
        (proEtaleSheafAdjunction g CommRingCat.{u + 1})).comp
          (proEtaleSheafAdjunction f CommRingCat.{u + 1})) _,
    conjugateIsoEquiv_trans _
      ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
        (proEtaleSheafAdjunction (f ≫ g) CommRingCat.{u + 1})) _]
  simp only [ringCompAt_conjugate, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator, Iso.trans_assoc]
  exact directCompAt_assoc f g h fgh hfgh

private theorem ringCompAt_assoc_app {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    (ringCompAt f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app R ≫
        (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((ringCompAt g h gh hgh).hom.app R) =
      (ringCompAt fg h fgh hfgh).hom.app R ≫
        (ringCompAt f g fg hfg).hom.app
          ((proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R) := by
  subst fg
  subst gh
  subst fgh
  have key := congr_app (congrArg Iso.hom
    (ringCompAt_assoc f g h ((f ≫ g) ≫ h) (Category.assoc f g h))) R
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] using key

private def faceCoefficient {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {j : Y' ⟶ Y}
    (sq : CommSq a b f j)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    (proEtaleSheafInverseImage b CommRingCat.{u + 1}).obj
        ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R) ≅
      (proEtaleSheafInverseImage a CommRingCat.{u + 1}).obj S :=
  ((ringCompAt b j (a ≫ f) sq.w).app R).symm ≪≫
    (ringCompAt a f (a ≫ f) rfl).app R ≪≫
    (proEtaleSheafInverseImage a CommRingCat.{u + 1}).mapIso c

private theorem faceCoefficient_coherent {X' X Y' Y : Scheme.{u}}
    {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {j : Y' ⟶ Y}
    (sq : CommSq a b f j)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    HEq (proEtaleRingCompositeCoefficients a f R S
      ((proEtaleSheafInverseImage a CommRingCat.{u + 1}).obj S) c (Iso.refl _))
      (proEtaleRingCompositeCoefficients b j R
        ((proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R)
        ((proEtaleSheafInverseImage a CommRingCat.{u + 1}).obj S)
        (Iso.refl _) (faceCoefficient sq R S c)) := by
  refine (ringComposite_heq a f (a ≫ f) rfl R S _ c (Iso.refl _)).trans ?_
  refine (heq_of_eq ?_).trans
    (ringComposite_heq b j (a ≫ f) sq.w R _ _ (Iso.refl _)
      (faceCoefficient sq R S c)).symm
  apply Iso.ext
  simp [faceCoefficient]

private theorem faceCoefficient_compAt
    {Z X Y ZU XU YU : Scheme.{u}}
    {g : Z ⟶ X} {f : X ⟶ Y} {gU : ZU ⟶ XU} {fU : XU ⟶ YU}
    {jZ : ZU ⟶ Z} {jX : XU ⟶ X} {jY : YU ⟶ Y}
    (sf : CommSq jX fU f jY) (sg : CommSq jZ gU g jX)
    (q : Z ⟶ Y) (qU : ZU ⟶ YU) (hq : q = g ≫ f) (hqU : qU = gU ≫ fU)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (T : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (d : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj S ≅ T) :
    (ringCompAt gU fU qU hqU).app
        ((proEtaleSheafInverseImage jY CommRingCat.{u + 1}).obj R) ≪≫
      (proEtaleSheafInverseImage gU CommRingCat.{u + 1}).mapIso
        (faceCoefficient sf R S c) ≪≫ faceCoefficient sg S T d =
    faceCoefficient
      (show CommSq jZ qU q jY from ⟨by
        rw [hq, hqU, ← Category.assoc, sg.w, Category.assoc, sf.w, Category.assoc]⟩)
      R T ((ringCompAt g f q hq).app R ≪≫
        (proEtaleSheafInverseImage g CommRingCat.{u + 1}).mapIso c ≪≫ d) := by
  have hout : jZ ≫ q = qU ≫ jY := by
    rw [hq, hqU, ← Category.assoc, sg.w, Category.assoc, sf.w, Category.assoc]
  have h1 := ringCompAt_assoc_app gU fU jY qU (jX ≫ f) (jZ ≫ q)
    hqU sf.w hout R
  have h2 := ringCompAt_assoc_app gU jX f (jZ ≫ g) (jX ≫ f) (jZ ≫ q)
    sg.w rfl (by rw [hq, Category.assoc]) R
  have h3 := ringCompAt_assoc_app jZ g f (jZ ≫ g) q (jZ ≫ q)
    rfl hq (by rw [hq, Category.assoc]) R
  have h1' :
      (ringCompAt gU fU qU hqU).hom.app
          ((proEtaleSheafInverseImage jY CommRingCat.{u + 1}).obj R) ≫
        (proEtaleSheafInverseImage gU CommRingCat.{u + 1}).map
          ((ringCompAt fU jY (jX ≫ f) sf.w).inv.app R) =
      (ringCompAt qU jY (jZ ≫ q) hout).inv.app R ≫
        (ringCompAt gU (jX ≫ f) (jZ ≫ q)
          (by rw [hq, ← Category.assoc, sg.w, Category.assoc])).hom.app R := by
    apply (cancel_epi ((ringCompAt qU jY (jZ ≫ q) hout).hom.app R)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% h1]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  apply Iso.ext
  simp only [faceCoefficient, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1']
  simp only [← Functor.map_comp]
  rw [reassoc_of% h2]
  rw [← Functor.comp_map]
  rw [← (ringCompAt gU jX (jZ ≫ g) sg.w).hom.naturality_assoc]
  rw [Iso.hom_inv_id_app_assoc]
  rw [(ringCompAt jZ g (jZ ≫ g) rfl).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← reassoc_of% h3]
  simp only [Functor.map_comp]


private def chosenOfPullback {A B C D : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ D} {d : C ⟶ D}
    (h : IsPullback a b c d) : ChosenCartesianSquare a b c d where
  w := h.w
  isoPullback := h.isoPullback
  hom_fst := h.isoPullback_hom_fst
  hom_snd := h.isoPullback_hom_snd

private structure CubeGeometry {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) {U : Scheme.{u}} (j : U ⟶ Y) where
  XU : Scheme.{u}
  YU' : Scheme.{u}
  XU' : Scheme.{u}
  jX : XU ⟶ X
  jY' : YU' ⟶ Y'
  jX' : XU' ⟶ X'
  fU : XU ⟶ U
  gU : YU' ⟶ U
  fU' : XU' ⟶ YU'
  gU' : XU' ⟶ XU
  localSquare : ChosenCartesianSquare gU' fU' fU gU
  sourceSquare : ChosenCartesianSquare jX fU f j
  targetSquare : ChosenCartesianSquare jX' fU' f' jY'
  baseSquare : ChosenCartesianSquare jY' gU g j
  upperSquare : ChosenCartesianSquare jX' gU' g' jX

private def cubeGeometry {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) {U : Scheme.{u}} (j : U ⟶ Y) :
    CubeGeometry sq j := by
  let A := pullback f j
  let B := pullback g j
  let q := g' ≫ f
  let D := pullback q j
  let a : D ⟶ A := pullback.lift (pullback.fst q j ≫ g') (pullback.snd q j)
    (by simpa only [Category.assoc] using pullback.condition (f := q) (g := j))
  let b : D ⟶ B := pullback.lift (pullback.fst q j ≫ f') (pullback.snd q j)
    (by rw [Category.assoc, ← sq.w]; exact pullback.condition)
  have ha : a ≫ pullback.fst f j = pullback.fst q j ≫ g' := by simp [a]
  have hb : b ≫ pullback.fst g j = pullback.fst q j ≫ f' := by simp [b]
  have hau : a ≫ pullback.snd f j = pullback.snd q j := by simp [a]
  have hbu : b ≫ pullback.snd g j = pullback.snd q j := by simp [b]
  have hsource := IsPullback.of_hasPullback f j
  have hbase := IsPullback.of_hasPullback g j
  have hupper : IsPullback (pullback.fst q j) a g' (pullback.fst f j) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd f j) (v₂₂ := f)
      (h₃₁ := j)
    · simpa only [hau] using IsPullback.of_hasPullback q j
    · exact ha.symm
    · exact hsource
  have htarget : IsPullback (pullback.fst q j) b f' (pullback.fst g j) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd g j) (v₂₂ := g)
      (h₃₁ := j)
    · simpa only [hbu, ← sq.w] using IsPullback.of_hasPullback q j
    · exact hb.symm
    · exact hbase
  have horiginal := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
    sq.hom_fst sq.hom_snd
  have hlocal : IsPullback a b (pullback.snd f j) (pullback.snd g j) := by
    have hout := htarget.paste_horiz horiginal
    rw [← ha, hbase.w] at hout
    exact hout.of_right (hau.trans hbu.symm) hsource
  exact
    { XU := A
      YU' := B
      XU' := D
      jX := pullback.fst f j
      jY' := pullback.fst g j
      jX' := pullback.fst q j
      fU := pullback.snd f j
      gU := pullback.snd g j
      fU' := b
      gU' := a
      localSquare := chosenOfPullback hlocal
      sourceSquare := cartesian f j
      targetSquare := chosenOfPullback htarget
      baseSquare := cartesian g j
      upperSquare := chosenOfPullback hupper }

private theorem cubeExists
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {U : Scheme.{u}} (j : U ⟶ Y) :
    Nonempty (OpenCube r j) := by
  let G := cubeGeometry sq j
  let RU := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj r.RY
  let RXU := (proEtaleSheafInverseImage G.jX CommRingCat.{u + 1}).obj r.RX
  let RYU' := (proEtaleSheafInverseImage G.jY' CommRingCat.{u + 1}).obj r.RY'
  let RXU' := (proEtaleSheafInverseImage G.jX' CommRingCat.{u + 1}).obj r.RX'
  let cfU := faceCoefficient G.sourceSquare.toCommSq r.RY r.RX r.cf
  let cgU := faceCoefficient G.baseSquare.toCommSq r.RY r.RY' r.cg
  let cfU' := faceCoefficient G.targetSquare.toCommSq r.RY' r.RX' r.cf'
  let cgU' := faceCoefficient G.upperSquare.toCommSq r.RX r.RX' r.cg'
  have old :
      (ringCompAt g' f (g' ≫ f) rfl).app r.RY ≪≫
        (proEtaleSheafInverseImage g' CommRingCat.{u + 1}).mapIso r.cf ≪≫ r.cg' =
      (ringCompAt f' g (g' ≫ f) sq.w).app r.RY ≪≫
        (proEtaleSheafInverseImage f' CommRingCat.{u + 1}).mapIso r.cg ≪≫ r.cf' := by
    exact eq_of_heq ((ringComposite_heq g' f (g' ≫ f) rfl
      r.RY r.RX r.RX' r.cf r.cg').symm.trans
      (r.coherent.trans (ringComposite_heq f' g (g' ≫ f) sq.w
        r.RY r.RY' r.RX' r.cg r.cf')))
  have hl := faceCoefficient_compAt G.sourceSquare.toCommSq G.upperSquare.toCommSq
    (g' ≫ f) (G.gU' ≫ G.fU) rfl rfl r.RY r.RX r.RX' r.cf r.cg'
  have hr := faceCoefficient_compAt G.baseSquare.toCommSq G.targetSquare.toCommSq
    (g' ≫ f) (G.gU' ≫ G.fU) sq.w G.localSquare.w
    r.RY r.RY' r.RX' r.cg r.cf'
  rw [old] at hl
  have hc : HEq (proEtaleRingCompositeCoefficients G.gU' G.fU RU RXU RXU' cfU cgU')
      (proEtaleRingCompositeCoefficients G.fU' G.gU RU RYU' RXU' cgU cfU') := by
    refine (ringComposite_heq G.gU' G.fU (G.gU' ≫ G.fU) rfl
      RU RXU RXU' cfU cgU').trans ?_
    refine (heq_of_eq (hl.trans hr.symm)).trans ?_
    exact (ringComposite_heq G.fU' G.gU (G.gU' ≫ G.fU) G.localSquare.w
      RU RYU' RXU' cgU cfU').symm
  exact ⟨{
    XU := G.XU
    YU' := G.YU'
    XU' := G.XU'
    jX := G.jX
    jY' := G.jY'
    jX' := G.jX'
    fU := G.fU
    gU := G.gU
    fU' := G.fU'
    gU' := G.gU'
    localSquare := G.localSquare
    sourceSquare := G.sourceSquare
    targetSquare := G.targetSquare
    baseSquare := G.baseSquare
    upperSquare := G.upperSquare
    localRings := {
      RY := RU, RX := RXU, RY' := RYU', RX' := RXU'
      cf := cfU, cg := cgU, cf' := cfU', cg' := cgU', coherent := hc }
    cj := Iso.refl _
    cjX := Iso.refl _
    cjY' := Iso.refl _
    cjX' := Iso.refl _
    sourceCoherent := faceCoefficient_coherent G.sourceSquare.toCommSq r.RY r.RX r.cf
    targetCoherent := faceCoefficient_coherent G.targetSquare.toCommSq r.RY' r.RX' r.cf'
    baseCoherent := faceCoefficient_coherent G.baseSquare.toCommSq r.RY r.RY' r.cg
    upperCoherent := faceCoefficient_coherent G.upperSquare.toCommSq r.RX r.RX' r.cg' }⟩


/-- Every open of the base admits the required actual base-change presentation.
No additional coefficient or geometric hypothesis is imposed by OpenCube.
Source: Stacks 09A5, 03CB and 00XZ
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: form the three base changes of j and the restricted Cartesian square using
fibre products. Put j⁻¹RY, jX⁻¹RX, jY'⁻¹RY', jX'⁻¹RX' at the local vertices. Inverse-image
composition defines each local coefficient comparison. Their coherence follows
from the projection-preserving fibre-product associativity and the original coefficient
coherence. This is the construction used in steps 6--7; it works also for empty opens. -/
theorem openCube_exists (r : StrictTowerRingedSquare sq) (j : U ⟶ Y)
    [IsOpenImmersion j] :
    Nonempty (OpenCube r j) := by
  exact cubeExists r j


/-- Restricting the global exchange equals the exchange of the restricted square,
through the specified open comparisons and canonical pullback-composition maps.
Source: Stacks 08FI, 09T5, 09A5, 03CB and 00XZ
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 7. Restrict a and b; their targets remain K-injective by open restriction.
The ordinary open comparison's counit equation rewrites the restricted counit as
the local counit preceded by the local inverse-image comparison. Taking the local
adjoint transpose consequently identifies restricted ordinary exchange with local
ordinary exchange after the p/open comparison. The coefficient and composition maps
agree by their shared projection-preserving fibre-product descriptions. Naturality of
the p'/open comparison with b identifies the final direct-image arrow. Localizing
these equal chain maps gives the displayed equality of derived morphisms. -/
theorem open_restriction (r : StrictTowerRingedSquare sq) [IsOpenImmersion j]
    (C : OpenCube r j)
    (K : DerivedCategory (proEtaleRingModules X r.RX)) :
    (basePull C.targetFace).mapDerivedCategory.map ((exchange r).app K) ≫
        (exchange C.targetFace).app ((upperPull r).mapDerivedCategory.obj K) ≫
        (targetPush C.localRings).rightDerivedFunctor.map
          ((pullSquare C.upperFace).inv.app K) =
      (pullSquare C.baseFace).inv.app ((verticalPush r).rightDerivedFunctor.obj K) ≫
        (basePull C.localRings).mapDerivedCategory.map ((exchange C.sourceFace).app K) ≫
        (exchange C.localRings).app ((upperPull C.sourceFace).mapDerivedCategory.obj K) := by
  simpa only [pullSquare] using restriction_exchange_cube r C K

/-- Invertibility descends from the exchanges on every member of a small base-open cover.
Source: Stacks 00XZ and sites-cohomology 0EYZ
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 8. The base changes of the covering opens cover Y'. On every pro-etale
object Q the corresponding inverse-image opens generate a covering sieve. The
open_restriction equality and the invertible open comparisons show that every
restriction of the global exchange along this sieve is invertible. Apply
proEtaleRingedOpenCover_reflectsIso for module sheaves over the actual ring on Y'.
This uses homology and the sheaf covering-sieve criterion in the unbounded derived category.
If the cover is empty, Y and Y' are empty and the same covering-sieve argument applies. -/
theorem open_descent (r : StrictTowerRingedSquare sq) (ι : Type (u + 1))
    (V : ι → Scheme.{u}) (jV : ∀ a : ι, V a ⟶ Y)
    [∀ a : ι, IsOpenImmersion (jV a)]
    (cover : ∀ y : Y, ∃ (a : ι) (x : V a), (jV a).base x = y)
    (C : ∀ a : ι, OpenCube r (jV a))
    (K : DerivedCategory (proEtaleRingModules X r.RX))
    (localIso : ∀ a : ι,
      IsIso ((exchange (C a).localRings).app
        ((upperPull (C a).sourceFace).mapDerivedCategory.obj K))) :
    IsIso ((exchange r).app K) := by
  have hopen (a : ι) : IsOpenImmersion (C a).jY' := by
    rw [← (C a).baseSquare.hom_fst]
    infer_instance
  have hcover : ∀ y : Y', ∃ (a : ι) (x : (C a).YU'), (C a).jY'.base x = y := by
    intro y
    obtain ⟨a, x, hx⟩ := cover (g y)
    have hy : y ∈ Set.range (pullback.fst g (jV a)) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨x, hx⟩
    obtain ⟨z, hz⟩ := hy
    refine ⟨a, (C a).baseSquare.isoPullback.inv z, ?_⟩
    change ((C a).baseSquare.isoPullback.inv ≫ (C a).jY') z = y
    have hh := congrArg
      (fun k : (C a).YU' ⟶ Y' ↦ (C a).baseSquare.isoPullback.inv ≫ k)
      (C a).baseSquare.hom_fst
    simp only [Iso.inv_hom_id_assoc] at hh
    exact (congrArg (fun k : pullback g (jV a) ⟶ Y' ↦ k z) hh.symm).trans hz
  apply proEtaleRingedOpenCover_reflectsIso r.RY' ι (fun a ↦ (C a).YU')
    (fun a ↦ (C a).jY') hcover (fun a ↦ (C a).localRings.RY') (fun a ↦ (C a).cjY')
  intro a
  have : IsIso (exchange (C a).sourceFace) :=
    (open_comparison (C a).sourceFace).2
  have : IsIso (exchange (C a).targetFace) :=
    (open_comparison (C a).targetFace).2
  have : IsIso ((exchange (C a).localRings).app
      ((upperPull (C a).sourceFace).mapDerivedCategory.obj K)) := localIso a
  have h := open_restriction r (C a) K
  have hi : IsIso
      ((pullSquare (C a).baseFace).inv.app ((verticalPush r).rightDerivedFunctor.obj K) ≫
        (basePull (C a).localRings).mapDerivedCategory.map
          ((exchange (C a).sourceFace).app K) ≫
        (exchange (C a).localRings).app
          ((upperPull (C a).sourceFace).mapDerivedCategory.obj K)) := by
    infer_instance
  rw [← h] at hi
  exact IsIso.of_isIso_comp_right
    ((basePull (C a).targetFace).mapDerivedCategory.map ((exchange r).app K))
    ((exchange (C a).targetFace).app ((upperPull r).mapDerivedCategory.obj K) ≫
      (targetPush (C a).localRings).rightDerivedFunctor.map
        ((pullSquare (C a).upperFace).inv.app K))

/-- The identity direct-image comparison is uniquely fixed on every section by the
actual identity fibre-product map. Source: Stacks 09A5 and 00XZ
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 9. The direct image on an object V is the module on V ×_X X. Restriction
along V → V ×_X X identifies it with the original module on V. These maps are linear
because the coefficient identity is the adjunction conjugate of the same site identity.
They are natural and inverse to restriction along the first projection. Equality on all
sections proves uniqueness, with no condition on the ring or scheme. -/
theorem identityDirect_existsUnique (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    ∃! e : proEtaleRingModuleDirectImage (𝟙 Z) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ≅ 𝟭 _,
      ∀ (M : proEtaleRingModules Z R) (V : Z.ProEt)
        (m : ((proEtaleRingModuleDirectImage (𝟙 Z) R R
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).obj M).val.obj (op V)),
        (e.hom.app M).val.app (op V) m =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Z).inv.app V).op m := by
  have : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ Z)).IsContinuous
      (ProEt.topology Z) (ProEt.topology Z) := Functor.isContinuous_id _
  let A := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let e := MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) Z
  let t : A ⟶ ((proEtaleBaseChange (𝟙 Z)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology Z)).obj A :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap (𝟙 Z) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have hc : proEtaleRingDirectImageMap (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} Z).inv.app R := by
    exact (unit_conjugateEquiv_symm Adjunction.id
      (proEtaleSheafAdjunction (𝟙 Z) CommRingCat.{u + 1})
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} Z).inv R).symm
  have ht : t ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv _ _ _).app A = 𝟙 A := by
    dsimp only [t]
    rw [hc]
    ext U x
    change (R.obj.map (e.hom.app U.unop).op ≫ R.obj.map (e.inv.app U.unop).op) x = x
    rw [← R.obj.map_comp, ← CategoryTheory.op_comp, Iso.inv_hom_id_app,
      CategoryTheory.op_id, R.obj.map_id]
    rfl
  let d : proEtaleRingModuleDirectImage (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ≅ 𝟭 _ :=
    SheafOfModules.pushforwardCongr₂ (φ := t) e.symm ht ≪≫
      SheafOfModules.pushforwardId A
  have hd : ∀ (M : proEtaleRingModules Z R) (V : Z.ProEt)
      (m : ((proEtaleRingModuleDirectImage (𝟙 Z) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).obj M).val.obj (op V)),
      (d.hom.app M).val.app (op V) m = M.val.map (e.inv.app V).op m := by
    intro M V m
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  ext M V m
  exact (hd' M V.unop m).trans (hd M V.unop m).symm

/-- The section-normalized identity direct image. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def identityDirect (Z : Scheme.{u}) (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    proEtaleRingModuleDirectImage (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ≅ 𝟭 _ :=
  (identityDirect_existsUnique Z R).exists.choose

/-- The identity inverse-image comparison is its adjunction conjugate, so has no
freely chosen natural automorphism. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def identityPull (Z : Scheme.{u}) (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ≅ 𝟭 _ :=
  ((proEtaleRingModuleAdjunction (𝟙 Z) R R
    (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).ofNatIsoRight
      (identityDirect Z R)).leftAdjointUniq Adjunction.id

/-- Exact localization of the normalized module identity. Source: Stacks 09T5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def identityDerivedPull (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    (proEtaleRingModulePullback (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (identityPull Z R) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- Canonical coefficient identities commute with any inverse-image coefficient map.
Source: Stacks 03CB and 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 9 and step 1. Both composites are the given coefficient map after the
unit-normalized identity compositor. The identity triangles for the sheaf adjunction
identify them. Naturality allows arbitrary isomorphic presentations of the coefficient. -/
theorem identityCoefficients_coherent {P T : Scheme.{u}} (p : P ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S) :
    HEq (proEtaleRingCompositeCoefficients (𝟙 P) p R S S c
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
      (proEtaleRingCompositeCoefficients p (𝟙 T) R R S
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c) := by
  have hl := ringComposite_heq (𝟙 P) p p (Category.id_comp p).symm R S S c
    (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)
  have hr := ringComposite_heq p (𝟙 T) p (Category.comp_id p).symm R R S
    (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c
  refine hl.trans ((heq_of_eq ?_).trans hr.symm)
  rw [ringCompAt_left, ringCompAt_right]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.isoWhiskerRight_hom]
  change (proEtaleRingInverseImageId P).inv.app
      ((proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R) ≫
      (proEtaleSheafInverseImage (𝟙 P) CommRingCat.{u + 1}).map c.hom ≫
      (proEtaleRingInverseImageId P).hom.app S =
    (proEtaleSheafInverseImage p CommRingCat.{u + 1}).map
      ((proEtaleRingInverseImageId T).inv.app R) ≫
      (proEtaleSheafInverseImage p CommRingCat.{u + 1}).map
        ((proEtaleRingInverseImageId T).hom.app R) ≫ c.hom
  rw [(proEtaleRingInverseImageId P).hom.naturality]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  change c.hom = _
  exact ((congrArg (fun k ↦ k ≫ c.hom)
    ((proEtaleSheafInverseImage p CommRingCat.{u + 1}).map_id R)).trans
      (Category.id_comp c.hom)).symm

/-- The coefficient presentation of the identity square, with the actual identity
ring comparisons. Source: Stacks 09A5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent). -/
def identityRings {P T : Scheme.{u}} (p : P ⟶ T)
    (s : ChosenCartesianSquare (𝟙 P) p p (𝟙 T))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S) :
    StrictTowerRingedSquare s where
  RY := R
  RX := S
  RY' := R
  RX' := S
  cf := c
  cg := AlgebraicGeometry.ProEtaleTensorComparison.ringId R
  cg' := AlgebraicGeometry.ProEtaleTensorComparison.ringId S
  cf' := c
  coherent := identityCoefficients_coherent p R S c

-- Normalize identity pullbacks through their sectionwise direct-image conjugates.
attribute [local irreducible] LocallyRingedSpace.comp PresheafedSpace.comp
  exchangeModuleComposition proEtaleRingCompositeCoefficients identityDirect
  proEtaleAmbientRingedPullbackComparison proEtaleRingDerivedAdjunction

private theorem identityPull_conjugate_aux {A : Type*} [Category A]
    {L R : A ⥤ A} (a : L ⊣ R) (e : R ≅ 𝟭 A) :
    (a.ofNatIsoRight e).leftAdjointUniq Adjunction.id = a.leftAdjointIdIso e := by
  apply Iso.ext_inv
  ext M
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateIsoEquiv, conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight]

private theorem identityPull_conjugate (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    conjugateIsoEquiv Adjunction.id
      (proEtaleRingModuleAdjunction (𝟙 Z) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R))
      (identityPull Z R) = (identityDirect Z R).symm := by
  unfold identityPull
  rw [identityPull_conjugate_aux]
  exact Equiv.apply_symm_apply _ _

private abbrev RingedArrow (A B : Scheme.{u})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}) :=
  Σ h : A ⟶ B, (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S

private abbrev arrowPull {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleRingModulePullback z.1 R S z.2

private abbrev arrowBase {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleBaseChange z.1

private abbrev arrowPush {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleRingModuleDirectImage z.1 R S z.2

private abbrev arrowAdj {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleRingModuleAdjunction z.1 R S z.2

private theorem conjugate_square_transport {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}}
    {z w : RingedArrow A B R S} (e : w = z)
    {L₁ L₂ : proEtaleRingModules B R ⥤ proEtaleRingModules A S}
    {R₁ R₂ : proEtaleRingModules A S ⥤ proEtaleRingModules B R}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (a : arrowPull z ≅ L₁) (b : arrowPull w ≅ L₂) :
    conjugateIsoEquiv a₁ a₂ (b.symm ≪≫ eqToIso (congrArg arrowPull e) ≪≫ a) =
      conjugateIsoEquiv a₁ (arrowAdj z) a ≪≫
        (eqToIso (congrArg arrowPush e)).symm ≪≫
          (conjugateIsoEquiv a₂ (arrowAdj w) b).symm := by
  cases e
  simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm]
  rw [conjugateIsoEquiv_trans _ (arrowAdj z) _, conjugateIsoEquiv_iso_symm]

private theorem direct_transport {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}}
    {z w : RingedArrow A B R S} (e : z = w)
    (N : proEtaleRingModules A S) (V : B.ProEt)
    (m : ((arrowPush z).obj N).val.obj (op V)) :
    ((eqToIso (congrArg arrowPush e)).hom.app N).val.app (op V) m =
      N.val.map ((eqToIso (congrArg arrowBase e)).inv.app V).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

private theorem identityDirect_hom_sections (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (N : proEtaleRingModules Z R) (V : Z.ProEt)
    (m : ((proEtaleRingModuleDirectImage (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).obj N).val.obj (op V)) :
    ((identityDirect Z R).hom.app N).val.app (op V) m =
      N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Z).inv.app V).op m := by
  simpa only [identityDirect] using
    (identityDirect_existsUnique Z R).exists.choose_spec N V m

private theorem identityDirect_inv_sections (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (N : proEtaleRingModules Z R) (V : Z.ProEt) (m : N.val.obj (op V)) :
    ((identityDirect Z R).inv.app N).val.app (op V) m =
      N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Z).hom.app V).op m := by
  have : IsIso (((identityDirect Z R).hom.app N).val.app (op V)) := by
    change IsIso ((SheafOfModules.evaluation _ (op V)).map
      ((identityDirect Z R).hom.app N))
    infer_instance
  apply (ConcreteCategory.bijective_of_isIso
    (((identityDirect Z R).hom.app N).val.app (op V))).1
  have hi := congrArg (fun k ↦ k.val.app (op V) m)
    ((identityDirect Z R).inv_hom_id_app N)
  change ((identityDirect Z R).hom.app N).val.app (op V)
    (((identityDirect Z R).inv.app N).val.app (op V) m) = m at hi
  rw [hi, identityDirect_hom_sections]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, Iso.inv_hom_id_app]
  simp

private theorem baseCongr_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) e =
      eqToIso (congrArg (fun q ↦ proEtaleBaseChange q) e) := by
  cases e
  exact MorphismProperty.Over.pullbackCongr_refl (P := @WeaklyEtale) (Q := ⊤) f rfl

private theorem site_identity {P T : Scheme.{u}} (p : P ⟶ T)
    (e : p ≫ 𝟙 T = 𝟙 P ≫ p) (V : T.ProEt) :
    (eqToIso (congrArg (fun q ↦ proEtaleBaseChange q) e)).hom.app V ≫
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) (𝟙 P) p).hom.app V =
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) p (𝟙 T)).hom.app V ≫
      (proEtaleBaseChange p).map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app V) ≫
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
        ((proEtaleBaseChange p).obj V) := by
  rw [MorphismProperty.Over.pullbackComp_id_left p (𝟙 P ≫ p) rfl,
    MorphismProperty.Over.pullbackComp_id_right p (p ≫ 𝟙 T) rfl]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  rw [baseCongr_eq, baseCongr_eq]
  rw [← Category.assoc]
  apply (cancel_mono ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
    ((proEtaleBaseChange p).obj V))).mpr
  rw [← NatTrans.comp_app, ← Iso.trans_hom, eqToIso_trans]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward false in
private theorem localized_identity_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (B : C ⥤ C) (H : D ⥤ D)
    [F.Additive] [B.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (b : B ≅ 𝟭 C) (h : H ≅ 𝟭 D) (θ : B ⋙ F ≅ F ⋙ H)
    (hθ : θ ≪≫ Functor.isoWhiskerLeft F h ≪≫ F.rightUnitor =
      Functor.isoWhiskerRight b F ≪≫ F.leftUnitor)
    (M : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso θ).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso h ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
          (F.mapDerivedCategory.obj M) =
      F.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso b ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app M) := by
  have hl := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F h) M
  have hr := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight b F) M
  have hul := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) M
  have hur := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hl hr hul hur
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso B F).hom.app M)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hl, ← reassoc_of% hr, hur, hul]
  have he := congr_app (congrArg Iso.hom (congrArg
    (fun e ↦ Functor.mapDerivedCategoryNatIso e) hθ)) M
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at he
  have hleft : (Functor.mapDerivedCategoryNatIso F.leftUnitor).hom = 𝟙 _ := by
    exact Functor.mapDerivedCategoryNatIso_refl
  have hright : (Functor.mapDerivedCategoryNatIso F.rightUnitor).hom = 𝟙 _ := by
    exact Functor.mapDerivedCategoryNatIso_refl
  erw [Category.comp_id, Category.comp_id]
  simpa only [hleft, hright, NatTrans.id_app, Category.comp_id] using he

private theorem identity_mate {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (B : C ⥤ C) (H : D ⥤ D) (b : B ≅ 𝟭 C) (h : H ≅ 𝟭 D)
    (θ : B ⋙ L ≅ L ⋙ H)
    (hθ : ∀ M, θ.hom.app M ≫ h.hom.app (L.obj M) = L.map (b.hom.app M)) (M : D) :
    (mateEquiv a a (TwoSquare.mk B L L H θ.hom)).natTrans.app M ≫
        R.map (h.hom.app M) = b.hom.app (R.obj M) := by
  dsimp [mateEquiv]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  change a.unit.app (B.obj (R.obj M)) ≫ R.map (θ.hom.app (R.obj M)) ≫
    R.map (H.map (a.counit.app M)) ≫ R.map (h.hom.app M) = _
  have hn := h.hom.naturality (a.counit.app M)
  simp only [Functor.id_map] at hn
  have hn' : H.map (a.counit.app M) ≫ h.hom.app M =
      h.hom.app (L.obj (R.obj M)) ≫ a.counit.app M := hn
  rw [← R.map_comp]
  rw [hn']
  rw [R.map_comp, ← R.map_comp_assoc, hθ]
  change a.unit.app (B.obj (R.obj M)) ≫ (L ⋙ R).map (b.hom.app (R.obj M)) ≫
    R.map (a.counit.app M) = _
  rw [← a.unit.naturality_assoc]
  simp only [Functor.id_map, Functor.id_obj]
  rw [a.right_triangle_components]
  simp

private theorem localized_exchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) :
    exchange r =
      (mateEquiv (proEtaleRingDerivedAdjunction f r.RY r.RX r.cf)
        (proEtaleRingDerivedAdjunction f' r.RY' r.RX' r.cf')
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso r.exchangeModuleSquare).hom)).natTrans := by
  unfold exchange proEtaleAmbientRingedExchange
  rw [r.ambientSquare_localization]

private theorem left_square_of_conjugate {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {B BR : C ⥤ C} {H HR : D ⥤ D} (aB : B ⊣ BR) (aH : H ⊣ HR)
    (b : B ≅ 𝟭 C) (h : H ≅ 𝟭 D) (db : BR ≅ 𝟭 C) (dh : HR ≅ 𝟭 D)
    (hb : conjugateIsoEquiv Adjunction.id aB b = db.symm)
    (hh : conjugateIsoEquiv Adjunction.id aH h = dh.symm)
    (θ : B ⋙ L ≅ L ⋙ H)
    (hθ : conjugateIsoEquiv (a.comp aH) (aB.comp a) θ =
      Functor.isoWhiskerRight dh R ≪≫ R.leftUnitor ≪≫ R.rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft R db.symm) :
    θ ≪≫ Functor.isoWhiskerLeft L h ≪≫ L.rightUnitor =
      Functor.isoWhiskerRight b L ≪≫ L.leftUnitor := by
  apply (conjugateIsoEquiv a (aB.comp a)).injective
  rw [conjugateIsoEquiv_trans a (a.comp aH) (aB.comp a),
    conjugateIsoEquiv_trans a (a.comp Adjunction.id) (a.comp aH),
    conjugateIsoEquiv_rightUnitor, conjugateIsoEquiv_isoWhiskerLeft, hh, hθ]
  rw [conjugateIsoEquiv_trans a (Adjunction.id.comp a) (aB.comp a),
    conjugateIsoEquiv_leftUnitor, conjugateIsoEquiv_isoWhiskerRight, hb]
  ext M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, Iso.symm_hom,
    Category.id_comp, Category.assoc]
  erw [← R.map_comp_assoc, Iso.inv_hom_id_app, R.map_id, Category.id_comp]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
set_option maxHeartbeats 2000000 in
-- Section comparisons reduce the chosen site pullbacks and their module structures.
private theorem identity_square_conjugate_aux {P T : Scheme.{u}} (p : P ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S)
    (a : proEtaleRingModulePullback (𝟙 P ≫ p) R S
        (proEtaleRingCompositeCoefficients (𝟙 P) p R S S c
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)) ≅
      proEtaleRingModulePullback p R S c ⋙ proEtaleRingModulePullback (𝟙 P) S S
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
    (b : proEtaleRingModulePullback (p ≫ 𝟙 T) R S
        (proEtaleRingCompositeCoefficients p (𝟙 T) R R S
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c) ≅
      proEtaleRingModulePullback (𝟙 T) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ⋙
          proEtaleRingModulePullback p R S c)
    (e : (⟨p ≫ 𝟙 T, proEtaleRingCompositeCoefficients p (𝟙 T) R R S
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c⟩ : RingedArrow P T R S) =
      ⟨𝟙 P ≫ p, proEtaleRingCompositeCoefficients (𝟙 P) p R S S c
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)⟩)
    (ha : ExchangeModuleCompositionNormalized (𝟙 P) p R S S c
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId S) a)
    (hb : ExchangeModuleCompositionNormalized p (𝟙 T) R R S
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c b) :
    conjugateIsoEquiv
      ((proEtaleRingModuleAdjunction p R S c).comp
        (proEtaleRingModuleAdjunction (𝟙 P) S S
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)))
      ((proEtaleRingModuleAdjunction (𝟙 T) R R
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).comp
        (proEtaleRingModuleAdjunction p R S c))
      (b.symm ≪≫ eqToIso (congrArg arrowPull e) ≪≫ a) =
      Functor.isoWhiskerRight (identityDirect P S)
          (proEtaleRingModuleDirectImage p R S c) ≪≫
        Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft (proEtaleRingModuleDirectImage p R S c)
          (identityDirect T R).symm := by
  let ah := (proEtaleRingModuleAdjunction p R S c).comp
    (proEtaleRingModuleAdjunction (𝟙 P) S S
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
  let ab := (proEtaleRingModuleAdjunction (𝟙 T) R R
    (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).comp
    (proEtaleRingModuleAdjunction p R S c)
  let z : RingedArrow P T R S := ⟨𝟙 P ≫ p, proEtaleRingCompositeCoefficients
    (𝟙 P) p R S S c (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)⟩
  let w : RingedArrow P T R S := ⟨p ≫ 𝟙 T, proEtaleRingCompositeCoefficients
    p (𝟙 T) R R S (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c⟩
  let da := conjugateIsoEquiv ah (arrowAdj z) a
  let db := conjugateIsoEquiv ab (arrowAdj w) b
  let t := (eqToIso (congrArg arrowPush e)).symm
  have hc := conjugate_square_transport e ah ab a b
  change conjugateIsoEquiv ah ab (b.symm ≪≫
    eqToIso (congrArg arrowPull e) ≪≫ a) = _
  rw [hc]
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply (cancel_mono (db.hom.app N)).mp
  change (da.hom.app N ≫ t.hom.app N ≫ db.inv.app N) ≫ db.hom.app N = _
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  erw [Category.id_comp ((identityDirect T R).inv.app
    ((proEtaleRingModuleDirectImage p R S c).obj N) ≫ db.hom.app N)]
  ext V m
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change (t.hom.app N).val.app V ((da.hom.app N).val.app V m) =
    (db.hom.app N).val.app V (((identityDirect T R).inv.app
      ((proEtaleRingModuleDirectImage p R S c).obj N)).val.app V
      ((((proEtaleRingModuleDirectImage p R S c).map
        ((identityDirect P S).hom.app N)).val.app V) m))
  have hda := ha N V.unop m
  change (da.hom.app N).val.app V m = _ at hda
  rw [hda]
  have htr := direct_transport e.symm N V.unop
    (N.val.map ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
      (𝟙 P) p).hom.app V.unop).op m)
  change (t.hom.app N).val.app V
      (N.val.map ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
        (𝟙 P) p).hom.app V.unop).op m) = _ at htr
  rw [htr]
  have hidP := identityDirect_hom_sections P S N ((proEtaleBaseChange p).obj V.unop) m
  change (((proEtaleRingModuleDirectImage p R S c).map
    ((identityDirect P S).hom.app N)).val.app V) m = _ at hidP
  rw [hidP]
  have hidT := identityDirect_inv_sections T R
    ((proEtaleRingModuleDirectImage p R S c).obj N) V.unop
    (N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
      ((proEtaleBaseChange p).obj V.unop)).op m)
  rw [hidT]
  have hdb := hb N V.unop
    (N.val.map ((proEtaleBaseChange p).map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app V.unop)).op
      (N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
        ((proEtaleBaseChange p).obj V.unop)).op m))
  change (db.hom.app N).val.app V _ = _ at hdb
  erw [hdb]
  set_option backward.isDefEq.respectTransparency false in
  have hcombine :
      N.val.map ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          p (𝟙 T)).hom.app V.unop).op
        (N.val.map ((proEtaleBaseChange p).map
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app V.unop)).op
          (N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
            ((proEtaleBaseChange p).obj V.unop)).op m)) =
      N.val.map (((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          p (𝟙 T)).hom.app V.unop) ≫
        (proEtaleBaseChange p).map
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app V.unop) ≫
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
          ((proEtaleBaseChange p).obj V.unop)).op m := by
    simp only [op_comp, PresheafOfModules.map_comp_apply]
    rfl
  rw [hcombine]
  simp only [← PresheafOfModules.map_comp_apply, ← op_comp]
  apply congrArg (fun k : (proEtaleBaseChange (p ≫ 𝟙 T)).obj V.unop ⟶
      (proEtaleBaseChange (𝟙 P)).obj ((proEtaleBaseChange p).obj V.unop) ↦
    N.val.map k.op m)
  change (eqToIso (congrArg (fun q ↦ proEtaleBaseChange q)
      (congrArg Sigma.fst e))).hom.app V.unop ≫
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) (𝟙 P) p).hom.app
        V.unop =
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) p (𝟙 T)).hom.app V.unop ≫
        (proEtaleBaseChange p).map
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app V.unop) ≫
        (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
          ((proEtaleBaseChange p).obj V.unop)
  exact site_identity p (congrArg Sigma.fst e) V.unop

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward false in
set_option maxHeartbeats 2000000 in
-- Instantiate the conjugation identity with the chosen coefficient compositors.
private theorem identity_square {P T : Scheme.{u}} (p : P ⟶ T)
    (s : ChosenCartesianSquare (𝟙 P) p p (𝟙 T))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S) :
    (identityRings p s R S c).exchangeModuleSquare ≪≫
        Functor.isoWhiskerLeft (proEtaleRingModulePullback p R S c) (identityPull P S) ≪≫
        Functor.rightUnitor _ =
      Functor.isoWhiskerRight (identityPull T R) (proEtaleRingModulePullback p R S c) ≪≫
        Functor.leftUnitor _ := by
  apply left_square_of_conjugate (proEtaleRingModuleAdjunction p R S c)
    (proEtaleRingModuleAdjunction (𝟙 T) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R))
    (proEtaleRingModuleAdjunction (𝟙 P) S S
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
    (identityPull T R) (identityPull P S) (identityDirect T R) (identityDirect P S)
    (identityPull_conjugate T R) (identityPull_conjugate P S)
  have hc := identity_square_conjugate_aux p R S c
    (exchangeModuleComposition (𝟙 P) p R S S c
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
    (exchangeModuleComposition p (𝟙 T) R R S
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c)
    (identityRings p s R S c).exchangeCoefficients_eq
    (by
      unfold exchangeModuleComposition
      exact (exchangeModuleComposition_existsUnique (𝟙 P) p R S S c
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)).choose_spec.1)
    (by
      unfold exchangeModuleComposition
      exact (exchangeModuleComposition_existsUnique p (𝟙 T) R R S
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c).choose_spec.1)
  simpa only [StrictTowerRingedSquare.exchangeModuleSquare, identityRings,
    Iso.trans_assoc] using hc

set_option backward.defeqAttrib.useBackward false in
set_option maxHeartbeats 2000000 in
-- Compare the concrete derived functors with the localized ordinary identity square.
/-- For the identity base change exchange is the identity under the canonical
identity and resolution comparisons. Source: Stacks 09A5 and 09T5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: normalize the ordinary identity square by conjugating its two compositors
and its coefficient transport. Their sectionwise formulas reduce to the identity
laws for fibre-product pullback. Exact localization preserves this equation and the
canonical identity comparisons. Naturality and the adjunction triangle then identify
the mate with the identity under these comparisons. Taking S = p⁻¹R and c = id gives
the node's coefficients. -/
theorem identity_normalization {P T : Scheme.{u}} (p : P ⟶ T)
    (s : ChosenCartesianSquare (𝟙 P) p p (𝟙 T))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S)
    (K : DerivedCategory (proEtaleRingModules P S)) :
    (exchange (identityRings p s R S c)).app K ≫
        (proEtaleRingDerivedDirectImage p R S c).map ((identityDerivedPull P S).hom.app K) =
      (identityDerivedPull T R).hom.app ((proEtaleRingDerivedDirectImage p R S c).obj K) := by
  let r := identityRings p s R S c
  have hl := localized_identity_square (proEtaleRingModulePullback p R S c)
    (basePull r) (upperPull r) (identityPull T R) (identityPull P S)
    r.exchangeModuleSquare (identity_square p s R S c)
  rw [localized_exchange]
  exact identity_mate (proEtaleRingDerivedAdjunction p R S c) _ _
    (identityDerivedPull T R) (identityDerivedPull P S) _ hl K

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
