/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.Paper.StrictTowerOperations
public import Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Sheaf.AlgebraicGeometry.RingedExchangeChainUnit
public import Sheaf.CategoryTheory.DerivedDegreeZeroExchangeEquation
public import Sheaf.AlgebraicGeometry.RingedUpperOpenPullbackKInjective
public import Sheaf.AlgebraicGeometry.RingedRestrictionOpenCube

public import Sheaf.AlgebraicGeometry.RingedOpenSquareUnitNormalization
import Sheaf.AlgebraicGeometry.RingedRestrictionDerivedCube
import Sheaf.AlgebraicGeometry.RingedOrdinaryOpenExchange
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenCoverReflectsIso
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
  sorry


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

/-- For the identity base change exchange is the identity under the canonical
identity and resolution comparisons. Source: Stacks 09A5 and 09T5
(blueprint: lem-sf-ringed-restriction-exchange-open-descent).
Proof: step 9. Use the same K-injective resolution on both sides and b = id. The
ordinary exchange is the identity after the specified module identity comparisons:
both its transpose and that of the identity are the counit. The adjunction triangle
proves their equality. Apply the resolution formula; its independence clause then
handles all other resolutions. Exact localization of the identity comparisons gives
precisely the equation below. Taking S = p⁻¹R and c = id gives the node's coefficients. -/
theorem identity_normalization {P T : Scheme.{u}} (p : P ⟶ T)
    (s : ChosenCartesianSquare (𝟙 P) p p (𝟙 T))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S)
    (K : DerivedCategory (proEtaleRingModules P S)) :
    (exchange (identityRings p s R S c)).app K ≫
        (proEtaleRingDerivedDirectImage p R S c).map ((identityDerivedPull P S).hom.app K) =
      (identityDerivedPull T R).hom.app ((proEtaleRingDerivedDirectImage p R S c).obj K) :=
  by sorry

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
