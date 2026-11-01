/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemEvaluationNormalizationData
import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.Ringed.RingedTopoiDerivedPullbackIndependentSupplement
import WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement

/-! # Restriction mates and their coherence

Source: Stacks Project, Tags 03D2, 0D6E and 07A6; Zheng, Construction 4.1.
(blueprint: lem-route-system-restriction-level-mate-invertibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.SystemEvaluationNormalization

universe a b c d va vb vc vd qA qB qA' qB'
variable {A : Type a} {B : Type b} {A' : Type c} {B' : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} A'] [Category.{vd} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{qA} A] [HasDerivedCategory.{qB} B]
  [HasDerivedCategory.{qA'} A'] [HasDerivedCategory.{qB'} B']
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  {U : A ⥤ A'} {V : B ⥤ B'} [U.Additive] [V.Additive]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientUnitNormalized (adj : L ⊣ R) (adj' : L' ⊣ R')
    (s : L ⋙ V ≅ U ⋙ L') : UnitNormalized adj adj' s := by
  intro M
  have h := Adjunction.derivedExact_mateEquiv_app_fac adj adj'
    (TwoSquare.mk _ _ _ _ s.inv)
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso s).inv)
    (by
      intro N
      have hs := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj s.symm N
      have hi := (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (L ⋙ V)) (.up ℤ)).inv_hom_id_app N
      rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
      simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app, hi,
        Category.id_comp, Category.comp_id] at hs
      rw [← cancel_epi (L'.mapDerivedCategoryFactorsh.inv.app
        ((U.mapHomotopyCategory (.up ℤ)).obj N) ≫
          L'.mapDerivedCategory.map (U.mapDerivedCategoryFactorsh.inv.app N))]
      simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
      erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
      simpa only [Category.assoc, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom,
        Iso.symm_inv, NatTrans.comp_app, Functor.mapDerivedCategorySquareIso,
        Functor.mapDerivedCategoryNatIso_symm] using hs) M
  dsimp only [UnitNormalized, derivedMate, ordinaryMate]
  erw [h]
  simp only [Iso.inv_hom_id_app_assoc]

end CategoryTheory.SystemEvaluationNormalization

namespace CategoryTheory.SystemEvaluationNormalization

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedCoefficientMate_isIso
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory A'] [HasDerivedCategory B']
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
    {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    {U : A ⥤ A'} {V : B ⥤ B'} [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : L ⋙ V ≅ U ⋙ L')
    [IsIso (ordinaryMate adj adj' s)]
    (hacyclic : ∀ I : CochainComplex B ℤ, I.IsKInjective →
      IsIso (R'.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient B' (.up ℤ)).obj
          ((V.mapHomologicalComplex (.up ℤ)).obj I)))) :
    IsIso (derivedMate adj adj' s) := by
  let α := derivedMate adj adj' s
  have hi (I : CochainComplex B ℤ) (hI : I.IsKInjective) :
      IsIso (α.app (DerivedCategory.Q.obj I)) := by
    let _ := hI
    have hR : IsIso (R.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient B (.up ℤ)).obj I)) := inferInstance
    have hR' : IsIso (R'.rightDerivedFunctorUnit.app
        ((V.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient B (.up ℤ)).obj I))) := hacyclic I hI
    have ho : IsIso
        (((ordinaryMate adj adj' s).mapHomotopyCategory (.up ℤ)).app
          ((HomotopyCategory.quotient B (.up ℤ)).obj I)) := by
      change IsIso ((HomotopyCategory.quotient A' (.up ℤ)).map
        (((ordinaryMate adj adj' s).mapHomologicalComplex (.up ℤ)).app I))
      have : IsIso (((ordinaryMate adj adj' s).mapHomologicalComplex (.up ℤ)).app I) := by
        change IsIso (((NatIso.mapHomologicalComplex
          (asIso (ordinaryMate adj adj' s)) (.up ℤ)).app I).hom)
        infer_instance
      exact (HomotopyCategory.quotient A' (.up ℤ)).map_isIso _
    have h := coefficientUnitNormalized adj adj' s
      ((HomotopyCategory.quotient B (.up ℤ)).obj I)
    have : IsIso
        (U.mapDerivedCategoryFactorsh.inv.app
            ((R.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient B (.up ℤ)).obj I)) ≫
          U.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient B (.up ℤ)).obj I)) ≫
          α.app (DerivedCategory.Q.obj I)) := by
      erw [h]
      exact IsIso.comp_isIso' (DerivedCategory.Qh.map_isIso _)
        (IsIso.comp_isIso' hR' (R'.rightDerivedFunctor.map_isIso _))
    have hleft : IsIso
        (U.mapDerivedCategoryFactorsh.inv.app
            ((R.mapHomotopyCategory (.up ℤ)).obj
              ((HomotopyCategory.quotient B (.up ℤ)).obj I)) ≫
          U.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient B (.up ℤ)).obj I))) :=
      IsIso.comp_isIso' (inferInstance : IsIso
        (U.mapDerivedCategoryFactorsh.inv.app _)) (U.mapDerivedCategory.map_isIso _)
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hleft
      (by simpa only [Category.assoc] using this)
  have hα (X : DerivedCategory B) : IsIso (α.app X) := by
    let K := DerivedCategory.Q.objPreimage X
    obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    let _ := hj
    let e : DerivedCategory.Q.obj I ≅ X :=
      (asIso (DerivedCategory.Q.map j)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso X
    exact (NatTrans.isIso_app_iff_of_iso α e).mp (hi I hI)
  exact NatIso.isIso_of_isIso_app α

end CategoryTheory.SystemEvaluationNormalization

namespace SheafOfModules

section CoefficientSquare

private abbrev coefficientModules {E : Type*} [Category* E]
    {τ : GrothendieckTopology E}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf τ CommRingCat.{w}) :=
  SheafOfModules.{w} ((sheafCompose τ (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

private abbrev coefficientSets {E : Type*} [Category* E] [EssentiallySmall.{w} E]
    {τ : GrothendieckTopology E}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (R : Sheaf τ CommRingCat.{w}) :=
  toSheaf ((sheafCompose τ (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
    sheafCompose τ (CategoryTheory.forget AddCommGrpCat.{w})

private abbrev coefficientRestriction {E : Type*} [Category* E]
    {τ : GrothendieckTopology E}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {R S : Sheaf τ CommRingCat.{w}} (a : R ⟶ S) :=
  restrictScalars ((sheafCompose τ (forget₂ CommRingCat.{w} RingCat.{w})).map a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Comparing underlying restriction functors unfolds the sheaf module constructions.
private theorem ordinaryCoefficientMate_isIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
    [EssentiallySmall.{w} D]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {AY BY : Sheaf J CommRingCat.{w}} {AX BX : Sheaf K CommRingCat.{w}}
    (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (IA : AlgebraicInverseImage uTop.inverse AY AX)
    (IB : AlgebraicInverseImage uTop.inverse BY BX)
    (aY : AY ⟶ BY) (aX : AX ⟶ BX)
    (ha : uTop.inverse.map
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map aY) ≫
        IB.ringUnderlying.hom = IA.ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map aX)
    {TY : coefficientModules AY ⥤ coefficientModules BY}
    {TX : coefficientModules AX ⥤ coefficientModules BX}
    (ay : TY ⊣ coefficientRestriction aY) (ax : TX ⊣ coefficientRestriction aX)
    {HB : coefficientModules BX ⥤ coefficientModules BY}
    {HA : coefficientModules AX ⥤ coefficientModules AY}
    (ab : IB.modules ⊣ HB) (aa : IA.modules ⊣ HA)
    (s : IB.modules ⋙ coefficientRestriction aX ≅
      coefficientRestriction aY ⋙ IA.modules)
    (hs : ∀ M : coefficientModules BY,
      (coefficientSets AX).map (s.hom.app M) ≫
          IA.moduleUnderlying.hom.app ((coefficientRestriction aY).obj M) =
        IB.moduleUnderlying.hom.app M) :
    IsIso (mateEquiv ab aa (TwoSquare.mk _ _ _ _ s.inv)).natTrans := by
  let _ := uTop.leftExact
  obtain ⟨e, he⟩ := ScalarIndependent.exists_scalarInverseImageIndependent
    uTop.inverse uTop.direct uTop.adj IA IB aY aX ha TY TX ay ax
  have hunit (M : coefficientModules AY) :
      IA.modules.map (ay.unit.app M) ≫ s.inv.app (TY.obj M) ≫
          (coefficientRestriction aX).map (e.hom.app M) =
        ax.unit.app (IA.modules.obj M) := by
    apply (coefficientSets AX).map_injective
    have hsinv : (coefficientSets AX).map (s.inv.app (TY.obj M)) =
        IA.moduleUnderlying.hom.app _ ≫ IB.moduleUnderlying.inv.app (TY.obj M) := by
      apply (cancel_epi ((coefficientSets AX).map (s.hom.app (TY.obj M)))).mp
      erw [← Functor.map_comp, Iso.hom_inv_id_app, (coefficientSets AX).map_id,
        ← Category.assoc, hs, Iso.hom_inv_id_app]
      rfl
    simp only [Functor.map_comp, hsinv, ← Category.assoc]
    erw [IA.moduleUnderlying.hom.naturality]
    simp only [Category.assoc]
    change IA.moduleUnderlying.hom.app M ≫
        (uTop.inverse.map ((coefficientSets AY).map (ay.unit.app M)) ≫
          IB.moduleUnderlying.inv.app (TY.obj M) ≫
          (coefficientSets BX).map (e.hom.app M)) =
      (coefficientSets AX).map (ax.unit.app (IA.modules.obj M))
    rw [he M, Iso.hom_inv_id_app_assoc]
  let δ := ((mateEquiv ay ax).symm (TwoSquare.mk _ _ _ _ s.inv)).natTrans
  have hδ : δ = e.inv := by
    apply NatTrans.ext
    funext M
    apply (cancel_mono (e.hom.app M)).mp
    rw [Iso.inv_hom_id_app]
    apply (ax.homEquiv _ _).injective
    rw [ax.homEquiv_naturality_right]
    have hh : ax.homEquiv _ _ (δ.app M) =
        IA.modules.map (ay.unit.app M) ≫ s.inv.app (TY.obj M) := by
      exact (unit_mateEquiv_symm ay ax (TwoSquare.mk _ _ _ _ s.inv) M).symm
    rw [hh, Category.assoc]
    exact (hunit M).trans (ax.homEquiv_id _).symm
  have hm : mateEquiv ay ax (TwoSquare.mk _ _ _ _ e.inv) =
      TwoSquare.mk _ _ _ _ s.inv := by
    have hh : TwoSquare.mk _ _ _ _ e.inv =
        (mateEquiv ay ax).symm (TwoSquare.mk _ _ _ _ s.inv) := by
      apply TwoSquare.ext
      intro M
      exact (congrArg (fun t ↦ t.app M) hδ).symm
    rw [hh, Equiv.apply_symm_apply]
  have hi : IsIso (conjugateEquiv (ay.comp ab) (aa.comp ax) e.inv) := inferInstance
  rw [← iterated_mateEquiv_conjugateEquiv ay ax aa ab
    (TwoSquare.mk _ _ _ _ e.inv), hm] at hi
  exact hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientFlatResolutions
    {E : Type*} [Category* E] [EssentiallySmall.{w} E]
    {τ : GrothendieckTopology E}
    [τ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify τ AddCommGrpCat.{w}] [τ.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (A : Sheaf τ CommRingCat.{w}) (K : HomotopyCategory (coefficientModules A) (.up ℤ)) :
    ∃ (P : HomotopyCategory (coefficientModules A) (.up ℤ)) (s : P ⟶ K),
      (CochainComplex.IsKFlatIndependentCoefficients (R := A) P.as ∧
        ∀ n : ℤ, IsFlatOnSite (R := A) (P.as.X n)) ∧
      HomotopyCategory.quasiIso (coefficientModules A) (.up ℤ) s := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨P, p, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  let _ := isMonoidal_W_independentCoefficients A
  let _ := monoidalCategory A
  have hf' (n : ℤ) : IsFlatOnSite (R := A) (P.X n) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso A (P.X n)).symm (hf n)
  exact ⟨(HomotopyCategory.quotient _ _).obj P, (HomotopyCategory.quotient _ _).map p,
    ⟨hp, hf'⟩, (HomotopyCategory.quotient_map_mem_quasiIso_iff p).mpr hq⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientRestriction_acyclic
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
    [EssentiallySmall.{w} D]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    {AY : Sheaf J CommRingCat.{w}} {AX BX : Sheaf K CommRingCat.{w}}
    (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (IA : AlgebraicInverseImage uTop.inverse AY AX)
    [IA.modules.Additive] [PreservesFiniteLimits IA.modules]
    [PreservesFiniteColimits IA.modules]
    (aX : AX ⟶ BX) (TX : coefficientModules AX ⥤ coefficientModules BX) [TX.Additive]
    (ax : TX ⊣ coefficientRestriction aX)
    (hinv : ∀ {P Q : CochainComplex (coefficientModules AX) ℤ} (f : P ⟶ Q),
      P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients → QuasiIso f →
        QuasiIso ((TX.mapHomologicalComplex (.up ℤ)).map f))
    (HA : coefficientModules AX ⥤ coefficientModules AY) [HA.Additive]
    (aa : IA.modules ⊣ HA)
    [Abelian.HasKInjectiveResolutions (coefficientModules AX)]
    (I : CochainComplex (coefficientModules BX) ℤ) (hI : I.IsKInjective)
    (T : CochainComplex (coefficientModules AX) ℤ) (hT : T.IsKInjective)
    (j : ((coefficientRestriction aX).mapHomologicalComplex (.up ℤ)).obj I ⟶ T)
    [QuasiIso j] : QuasiIso ((HA.mapHomologicalComplex (.up ℤ)).map j) := by
  let _ := uTop.leftExact
  let PB : ObjectProperty (HomotopyCategory (coefficientModules AX) (.up ℤ)) :=
    fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := AX) P.as
  let PE : ObjectProperty (HomotopyCategory (coefficientModules AY) (.up ℤ)) :=
    fun P ↦ CochainComplex.IsKFlatIndependentCoefficients (R := AY) P.as ∧
      ∀ n : ℤ, IsFlatOnSite (R := AY) (P.as.X n)
  have hresB (P : HomotopyCategory (coefficientModules AX) (.up ℤ)) :
      ∃ Q s, PB Q ∧ IsIso (DerivedCategory.Qh.map (s : Q ⟶ P)) := by
    obtain ⟨Q, s, hp, hs⟩ := coefficientFlatResolutions AX P
    exact ⟨Q, s, hp.1, Localization.inverts DerivedCategory.Qh _ _ hs⟩
  have hresE (P : HomotopyCategory (coefficientModules AY) (.up ℤ)) :
      ∃ Q s, PE Q ∧ IsIso (DerivedCategory.Qh.map (s : Q ⟶ P)) := by
    obtain ⟨Q, s, hp, hs⟩ := coefficientFlatResolutions AY P
    exact ⟨Q, s, hp, Localization.inverts DerivedCategory.Qh _ _ hs⟩
  have hinvf {P Q} (hP : PB P) (hQ : PB Q) (f : P ⟶ Q)
      (hf : IsIso (DerivedCategory.Qh.map f)) :
      IsIso (DerivedCategory.Qh.map ((TX.mapHomotopyCategory (.up ℤ)).map f)) := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    have hq : QuasiIso f := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mp
      ((DerivedCategory.isIso_Qh_map_iff _).mp hf)
    have ht := hinv f hP hQ hq
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh _ _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr ht)
  have hinvg {P Q} (_ : PE P) (_ : PE Q) (f : P ⟶ Q)
      (hf : IsIso (DerivedCategory.Qh.map f)) :
      IsIso (DerivedCategory.Qh.map ((IA.modules.mapHomotopyCategory (.up ℤ)).map f)) := by
    have hn := IA.modules.mapDerivedCategoryFactorsh.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    have : IsIso (IA.modules.mapDerivedCategory.map (DerivedCategory.Qh.map f)) :=
      IA.modules.mapDerivedCategory.map_isIso _
    have : IsIso (IA.modules.mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map ((IA.modules.mapHomotopyCategory (.up ℤ)).map f)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_left (IA.modules.mapDerivedCategoryFactorsh.hom.app P) _
  have hgood (P) (hP : PE P) : PB ((IA.modules.mapHomotopyCategory (.up ℤ)).obj P) := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    exact kFlat_inverseImage_independent uTop.inverse uTop.direct uTop.adj IA P hP.1 hP.2
  let _ := hI
  let _ := hT
  have hiso : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map j)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr (inferInstance : QuasiIso j)
  have hm := CategoryTheory.isIso_map_of_adjoints
    (ax.mapHomotopyCategory (.up ℤ)) (aa.mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso (coefficientModules AX) (.up ℤ))
    (HomotopyCategory.quasiIso (coefficientModules AY) (.up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh DerivedCategory.Qh PB PE hresB hresE hinvf hinvg hgood
    ((HomotopyCategory.quotient _ _).obj I)
    (fun P ↦ CochainComplex.IsKInjective.Qh_map_bijective P I)
    ((HomotopyCategory.quotient _ _).obj T)
    (fun P ↦ CochainComplex.IsKInjective.Qh_map_bijective P T)
    ((HomotopyCategory.quotient _ _).map j)
  have hq := (DerivedCategory.isIso_Qh_map_iff _).mp hm
  rw [Functor.mapHomotopyCategory_map] at hq
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp hq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientDerivedMate_isIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [EssentiallySmall.{w} C]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
    {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
    [EssentiallySmall.{w} D]
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    {AY BY : Sheaf J CommRingCat.{w}} {AX BX : Sheaf K CommRingCat.{w}}
    (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (IA : AlgebraicInverseImage uTop.inverse AY AX)
    (IB : AlgebraicInverseImage uTop.inverse BY BX)
    [IA.modules.Additive] [PreservesFiniteLimits IA.modules]
    [PreservesFiniteColimits IA.modules]
    [IB.modules.Additive] [PreservesFiniteLimits IB.modules]
    [PreservesFiniteColimits IB.modules]
    (aY : AY ⟶ BY) (aX : AX ⟶ BX)
    (ha : uTop.inverse.map
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map aY) ≫
        IB.ringUnderlying.hom = IA.ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map aX)
    {HB : coefficientModules BX ⥤ coefficientModules BY} [HB.Additive]
    {HA : coefficientModules AX ⥤ coefficientModules AY} [HA.Additive]
    [Abelian.HasKInjectiveResolutions (coefficientModules AX)]
    [Abelian.HasKInjectiveResolutions (coefficientModules BX)]
    (ab : IB.modules ⊣ HB) (aa : IA.modules ⊣ HA)
    (s : IB.modules ⋙ coefficientRestriction aX ≅
      coefficientRestriction aY ⋙ IA.modules)
    (hs : ∀ M : coefficientModules BY,
      (coefficientSets AX).map (s.hom.app M) ≫
          IA.moduleUnderlying.hom.app ((coefficientRestriction aY).obj M) =
        IB.moduleUnderlying.hom.app M) :
    IsIso (SystemEvaluationNormalization.derivedMate ab aa s) := by
  obtain ⟨TX, hTX, hmTX, haddTX, hinvTX, _⟩ :=
    derivedChangeOfRingsIndependentCoefficients aX
  let _ := haddTX
  obtain ⟨_, _, hoX⟩ := sheafRingCoefficientOrdinaryAdjunction aX
  obtain ⟨ax, _⟩ := hoX TX hTX hmTX
  obtain ⟨TY, hTY, hmTY, haddTY, _⟩ :=
    derivedChangeOfRingsIndependentCoefficients aY
  let _ := haddTY
  obtain ⟨_, _, hoY⟩ := sheafRingCoefficientOrdinaryAdjunction aY
  obtain ⟨ay, _⟩ := hoY TY hTY hmTY
  have hOrd := ordinaryCoefficientMate_isIso uTop IA IB aY aX ha ay ax ab aa s hs
  let _ : IsIso (SystemEvaluationNormalization.ordinaryMate ab aa s) := hOrd
  apply SystemEvaluationNormalization.derivedCoefficientMate_isIso ab aa s
  intro I hI
  obtain ⟨T, hT, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    (((coefficientRestriction aX).mapHomologicalComplex (.up ℤ)).obj I)
  let _ := hI
  let _ := hT
  let _ := hj
  have hq := coefficientRestriction_acyclic uTop IA aX TX ax hinvTX HA aa I hI T hT j
  let _ := hq
  let f := (HomotopyCategory.quotient _ (.up ℤ)).map j
  have hf : IsIso (DerivedCategory.Qh.map f) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hj
  have hg : IsIso (DerivedCategory.Qh.map ((HA.mapHomotopyCategory (.up ℤ)).map f)) := by
    dsimp only [f]
    rw [Functor.mapHomotopyCategory_map]
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr hq
  have hn := HA.rightDerivedFunctorUnit.naturality f
  dsimp only [Functor.comp_map] at hn
  have : IsIso (HA.rightDerivedFunctorUnit.app _ ≫
      HA.rightDerivedFunctor.map (DerivedCategory.Qh.map f)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (HA.rightDerivedFunctor.map (DerivedCategory.Qh.map f))

end CoefficientSquare

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [EssentiallySmall.{w} D]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (AY : Sheaf J CommRingCat.{w}) (AX : Sheaf K CommRingCat.{w})
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (aY : (Functor.const ℕᵒᵖ).obj AY ⟶ BY)
  (aX : (Functor.const ℕᵒᵖ).obj AX ⟶ BX)
  (uTop : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (IA : AlgebraicInverseImage uTop.inverse AY AX)
  (IB : ∀ n : ℕ, AlgebraicInverseImage uTop.inverse (BY.obj (op n)) (BX.obj (op n)))
  (FB : SystemGeometricInverseImageData BY BX uTop IB)
  (FA : SystemGeometricInverseImageData
    ((Functor.const ℕᵒᵖ).obj AY) ((Functor.const ℕᵒᵖ).obj AX) uTop (fun _ ↦ IA))

variable (Hn : ∀ n : ℕ, systemLevel BX n ⥤ systemLevel BY n)
  [∀ n : ℕ, (Hn n).Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel BX n)]
  (adjn : ∀ n : ℕ, FB.levelFunctor n ⊣ Hn n)
  (H0 : systemLevel ((Functor.const ℕᵒᵖ).obj AX) 0 ⥤
    systemLevel ((Functor.const ℕᵒᵖ).obj AY) 0) [H0.Additive]
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (systemLevel ((Functor.const ℕᵒᵖ).obj AX) n)]
  (adj0 : FA.levelFunctor 0 ⊣ H0)

/-- Normalized coefficient squares have invertible levelwise derived direct-image mates.

Source: Stacks Project, Tags 03D2, 03DA and 0D6E
(blueprint: lem-route-system-restriction-level-mate-invertibility).

Proof: Treat one compatible coefficient square at a time: the algebra maps aY_n, aX_n
with the level square d.level n, and the transition maps of BY, BX along h : n ≤ m with
d.restriction h. (1) Choose scalar-extension left adjoints T_Y, T_X of coefficient
restriction (derived change of rings with independent coefficients, Stacks 06YY). The
independently sized scalar inverse-image comparison gives e : T_Y ∘ I_B ≅ I_A ∘ T_X with
its unit equation on underlying sheaves; faithfulness of the underlying-sheaf functor and
the supplied levelUnderlying or restrictionUnderlying equation identify the mate of the
given square under the scalar adjunctions with e.inv. Iterated mating identifies the
ordinary direct-image mate with the conjugate of e.inv under the composite adjunctions,
so it is invertible. (2) For a K-injective complex I, the geometric right adjoint H_A
sends a K-injective resolution of the restriction of I to a quasi-isomorphism: apply the
resolving-adjunction argument of unbounded derived pushforward composition (Stacks 0D6E)
to scalar extension and exact inverse image, with K-flat resolutions with flat terms;
scalar extension inverts quasi-isomorphisms of K-flat complexes and inverse image keeps
such complexes K-flat. So the derived unit of H_A is invertible on the restricted
complex. (3) The exact-derived mate unit formula writes the localized ordinary mate
followed by the second derived unit as the first derived unit followed by the derived
mate; at a K-injective complex every other factor is invertible, so the derived mate is;
K-injective resolutions and naturality give it on every derived object. No flatness of
either coefficient map is used. -/
theorem systemRestrictionLevelMateInvertibility
    (htransition : ∀ {n m : ℕ} (h : n ≤ m),
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (BY.map (homOfLE h).op)) ≫ (IB n).ringUnderlying.hom =
        (IB m).ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map
            (BX.map (homOfLE h).op))
    (halgebra : ∀ n : ℕ,
      uTop.inverse.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{w})).map
          (aY.app (op n))) ≫ (IB n).ringUnderlying.hom =
        IA.ringUnderlying.hom ≫
          (sheafCompose K (CategoryTheory.forget CommRingCat.{w})).map (aX.app (op n)))
    (d : SystemNormalizationSquares AY AX BY BX aY aX uTop IA IB FB FA) :
    (∀ n : ℕ, IsIso (SystemEvaluationNormalization.derivedMate
      (adjn n) adj0 (d.level n))) ∧
    (∀ {n m : ℕ} (h : n ≤ m),
      IsIso (SystemEvaluationNormalization.derivedMate
        (adjn n) (adjn m) (d.restriction h))) := by
  let _ : Abelian.HasKInjectiveResolutions (coefficientModules AX) :=
    inferInstanceAs (Abelian.HasKInjectiveResolutions
      (systemLevel ((Functor.const ℕᵒᵖ).obj AX) 0))
  let _ : IA.modules.Additive := FA.levelAdditive 0
  let _ : PreservesFiniteLimits IA.modules := FA.levelLimits 0
  let _ : PreservesFiniteColimits IA.modules := FA.levelColimits 0
  let _ : ∀ n : ℕ, (IB n).modules.Additive := FB.levelAdditive
  let _ : ∀ n : ℕ, PreservesFiniteLimits (IB n).modules := FB.levelLimits
  let _ : ∀ n : ℕ, PreservesFiniteColimits (IB n).modules := FB.levelColimits
  constructor
  · intro n
    exact coefficientDerivedMate_isIso uTop IA (IB n) (aY.app (op n)) (aX.app (op n))
      (halgebra n) (adjn n) adj0 (d.level n) (d.levelUnderlying n)
  · intro n m h
    exact coefficientDerivedMate_isIso uTop (IB m) (IB n)
      (BY.map (homOfLE h).op) (BX.map (homOfLE h).op) (htransition h)
      (adjn n) (adjn m) (d.restriction h) (d.restrictionUnderlying h)

end SheafOfModules
