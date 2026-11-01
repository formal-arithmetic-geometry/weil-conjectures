/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import all WeilConjectures.ProperBaseChange.RingedAugmentedCechRestriction
import all WeilConjectures.ProperBaseChange.RingedLocalizationFactorRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.LocalizationCech.FlatLocalizationKoszulHomotopySupplement
import Mathlib.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.Algebra.Homology.InternalHom
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import WeilConjectures.ProperBaseChange.RingedKoszulFactorColimit
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationSheafExact
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all WeilConjectures.CategoryTheory.ProperBaseChange.LocalizationInverseImageCoherence
import all WeilConjectures.SixFunctors.InternalHomLocalizationComparison
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.SmoothPurity.HomComplexSectionsCochainsOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import all WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import all WeilConjectures.ProperBaseChange.ExtendedCechUnitIsoImpliesComplete
import WeilConjectures.Algebra.Homology.Site.SitePerfectModelRestrictionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # Local orthogonality of extended Cech complexes

Source: Stacks Project, dualizing.tex, Tag 0A6R, and sites-cohomology.tex,
Tags 0A94, 08JA and 08JB; the ringed-site extension is recorded in the DAG.
(blueprint: lem-weil-pbc-augmented-cech-local-orthogonality).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace CategoryTheory

/-- The intersection of all strictly full triangulated subcategories containing degree-zero
modules on which some ideal section acts invertibly. Invertibility is tested on every
section module on the slice, equivalently on the components of the scalar endomorphism.
There is no closure under arbitrary sums or retracts in this definition.
Source: Stacks Project, dualizing.tex, Tag 0A6R, localization orthogonality;
ringed-site formulation in the DAG.
(blueprint: lem-weil-pbc-augmented-cech-local-orthogonality). -/
def ringedIdealLocalizationTriangulated
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (V : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))] :
    ObjectProperty (ringedSiteDerived (O.over V)) :=
  fun A ↦ ∀ P : ObjectProperty (ringedSiteDerived (O.over V)),
    P.IsClosedUnderIsomorphisms → P.IsTriangulated →
      (∀ (M : ringedSiteModules.{u}
          ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))
        (x : I.val.obj (op V)),
        (∀ (W : C) (f : W ⟶ V), Function.Bijective
          (fun m : M.val.obj (op (Over.mk f)) ↦
            O.obj.map f.op (ι.val.app (op V) x) • m)) →
        P ((DerivedCategory.singleFunctor _ 0).obj M)) → P A

private theorem hom_zero_of_localization
    {A : Type*} [Category A] [HasZeroMorphisms A]
    (F : A ⥤ A) [F.PreservesZeroMorphisms] (η : 𝟭 A ⟶ F)
    {K M : A} (hK : IsZero (F.obj K)) [IsIso (η.app M)] (f : K ⟶ M) : f = 0 := by
  apply (cancel_mono (η.app M)).mp
  rw [zero_comp]
  change (𝟭 A).map f ≫ η.app M = 0
  rw [η.naturality, hK.eq_of_src (F.map f) 0, comp_zero]

private theorem sequence_zero_isIso
    {A : Type*} [Category A] {M : A} (s : M ⟶ M) [IsIso s]
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ s)))
    (hc : IsColimit c) : IsIso (c.ι.app 0) := by
  let d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ s)) :=
    { pt := M
      ι := NatTrans.ofSequence (fun n ↦ (show End M from inv s) ^ n) (by
        intro n
        simp only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
        rw [pow_succ, End.mul_def, ← Category.assoc]
        simp) }
  have hd : c.ι.app 0 ≫ hc.desc d = 𝟙 M := by
    calc
      c.ι.app 0 ≫ hc.desc d = d.ι.app 0 := hc.fac d 0
      _ = 𝟙 M := by simp [d]
  have he : hc.desc d ≫ c.ι.app 0 = 𝟙 c.pt := by
    apply hc.hom_ext
    intro n
    induction n with
    | zero =>
      simp only [← Category.assoc, hd, Category.comp_id]
      exact Category.id_comp _
    | succ n ih =>
      apply (cancel_epi s).mp
      have hstep : s ≫ c.ι.app (n + 1) = c.ι.app n := by
        simpa only [Functor.ofSequence_map_homOfLE_succ] using
          c.w (homOfLE (Nat.le_succ n))
      simpa only [← Category.assoc, hstep] using ih
  exact ⟨⟨hc.desc d, hd, he⟩⟩

private theorem localization_unit_isIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hs : ∀ V : Cᵒᵖ, Function.Bijective (fun x : M.val.obj V ↦ s.val V • x)) :
    IsIso ((scalarLocalizationUnit R s).app M) := by
  classical
  have hm : IsIso (localizationScalar R s M) := by
    let e : M.val ≅ M.val := PresheafOfModules.isoMk
      (fun V ↦ @asIso _ _ _ _ ((localizationScalar R s M).val.app V)
        ((ConcreteCategory.isIso_iff_bijective _).2 (hs V)))
      (fun {_ _} f ↦ (localizationScalar R s M).val.naturality f)
    have he : (localizationScalar R s M).val = e.hom := rfl
    let : IsIso ((SheafOfModules.forget _).map (localizationScalar R s M)) := by
      change IsIso (localizationScalar R s M).val
      rw [he]
      infer_instance
    exact isIso_of_reflects_iso _ (SheafOfModules.forget _)
  have hi := sequence_zero_isIso (localizationScalar R s M)
    (LocalizationSequence.moduleSheafCocone R s M)
    (LocalizationSequence.moduleSheafCoconeIsColimit R s M)
  simpa only [LocalizationSequence.moduleSheafCocone_zero] using hi

private theorem derived_unit_single_isIso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (F : A ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : 𝟭 A ⟶ F) (M : A) [IsIso (η.app M)] :
    IsIso ((Functor.mapDerivedCategoryNatTrans η).app
      ((DerivedCategory.singleFunctor A 0).obj M)) := by
  let P := (HomologicalComplex.single A (.up ℤ) 0).obj M
  have hterm (n : ℤ) : IsIso (η.app (P.X n)) := by
    by_cases hn : n = 0
    · subst n
      exact (NatTrans.isIso_app_iff_of_iso η
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M)).2 inferInstance
    · have hz : IsZero (P.X n) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      exact hz.isIso (F.map_isZero hz) _
  have hi : IsIso ((NatTrans.mapHomologicalComplex η (.up ℤ)).app P) := by
    let : ∀ n : ℤ, IsIso (((NatTrans.mapHomologicalComplex η (.up ℤ)).app P).f n) := hterm
    exact HomologicalComplex.Hom.isIso_of_components _
  have h := Functor.mapDerivedCategoryNatTrans_fac η P
  have hcomp : IsIso ((Functor.mapDerivedCategoryNatTrans η).app
      (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P) := by
    rw [h]
    infer_instance
  exact (isIso_comp_right_iff _ _).1 hcomp

private theorem exact_localization_orthogonal
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (F : A ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : 𝟭 A ⟶ F) (K : DerivedCategory A)
    (hK : IsZero (F.mapDerivedCategory.obj K)) (M : A) [IsIso (η.app M)] :
    (ObjectProperty.shiftClosure (fun X : DerivedCategory A ↦ X = K) ℤ).rightOrthogonal
      ((DerivedCategory.singleFunctor A 0).obj M) := by
  classical
  let ηD : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory :=
    (Functor.mapDerivedCategoryIdIso A).inv ≫ Functor.mapDerivedCategoryNatTrans η
  have := derived_unit_single_isIso F η M
  have hη : IsIso (ηD.app ((DerivedCategory.singleFunctor A 0).obj M)) := by
    dsimp only [ηD, NatTrans.comp_app]
    infer_instance
  rintro X f ⟨Y, n, e, hY⟩
  subst Y
  have hz : IsZero (F.mapDerivedCategory.obj X) :=
    ((shiftFunctor _ n).map_isZero hK).of_iso
      (F.mapDerivedCategory.mapIso e ≪≫ (F.mapDerivedCategory.commShiftIso n).app K)
  exact hom_zero_of_localization F.mapDerivedCategory ηD hz f

private noncomputable def localization_tensor_model
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (E : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses.{u, u, u} R s)))
    (hobj : ∀ N, E.obj N = changeOfRings (ringedLocalizationRingUnitOfUniverses.{u, u, u} R s) N)
    (hmap : ∀ {N N'} (f : N ⟶ N'), E.map f = eqToHom (hobj N) ≫
      changeOfRingsHom (ringedLocalizationRingUnitOfUniverses.{u, u, u} R s) N f ≫
        eqToHom (hobj N').symm) :
    scalarLocalization R s ≅ E ⋙
      SheafOfModules.scalarRestriction.{u, u, u}
        (ringedLocalizationRingUnitOfUniverses.{u, u, u} R s) := by
  classical
  letI : ∀ T : Sheaf J CommRingCat.{u},
      HasDerivedCategory.{u + 1} (SheafOfModules.scalarModules.{u, u, u} J T) :=
    fun T ↦ HasDerivedCategory.standard _
  let M := Classical.choice (scalarHomModels_exists.{u, u, u, u + 1} J)
  let a := ringedLocalizationRingUnitOfUniverses.{u, u, u} R s
  let i : E ≅ (M.scalar a).extension := NatIso.ofComponents
    (fun N ↦ eqToIso (hobj N) ≪≫ (eqToIso ((M.scalar a).extension_obj N)).symm)
    (by
      intro N N' f
      dsimp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
      rw [hmap, (M.scalar a).extension_map]
      simp [a, Category.assoc])
  exact localizationUnderlyingNatIso M R s ≪≫
    Functor.isoWhiskerRight i.symm (SheafOfModules.scalarRestriction.{u, u, u} a)

private theorem localized_cech_zero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (r : ℕ) (g : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (hs : ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧ ∀ (W : C) (a : W ⟶ V), S a →
      s.val (op W) ∈ Ideal.span (Set.range (fun i ↦ (g i).val (op W)))) :
    let := (scalarLocalization_exact R s).1
    let := (scalarLocalization_exact R s).2.1
    let := (scalarLocalization_exact R s).2.2
    IsZero ((scalarLocalization R s).mapDerivedCategory.obj
      (DerivedCategory.Q.obj (ringedExtendedCech R r g).1)) := by
  classical
  let B := ringedLocalizationRingOfUniverses.{u, u, u} R s
  let := HasDerivedCategory.standard (ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
  let m := Classical.choice
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel.{u, u, u, w, u + 1}
      (ringedLocalizationRingUnitOfUniverses.{u, u, u} R s))
  let U := SheafOfModules.scalarRestriction.{u, u, u}
    (ringedLocalizationRingUnitOfUniverses.{u, u, u} R s)
  let : PreservesFiniteLimits U := by
    let := HasDerivedCategory.standard (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    exact SheafOfModules.scalarRestriction_limits.{u, u, u, u + 1} _
  let : PreservesFiniteColimits U := by
    let := HasDerivedCategory.standard (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    exact SheafOfModules.scalarRestriction_colimits.{u, u, u, u + 1} _
  let P := (ringedExtendedCech R r g).1
  have hz : IsZero (m.T.obj (DerivedCategory.Q.obj P)) :=
    IsZero.of_iso (isZero_zero _) (Classical.choice
      (ringed_cech_localization_acyclic.{u, w, u + 1} R r g s hs))
  have hp : CochainComplex.IsKFlatIndependentCoefficients P :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 (cech_kflat R r g)
  have hε := m.computes P hp
  let e := localization_tensor_model R s m.E m.obj_eq m.map_eq
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (m.E ⋙ U)) (.up ℤ)).symm.app P
  let := (scalarLocalization_exact R s).1
  let := (scalarLocalization_exact R s).2.1
  let := (scalarLocalization_exact R s).2.2
  let d : (scalarLocalization R s).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅
      U.mapDerivedCategory.obj (m.T.obj (DerivedCategory.Q.obj P)) :=
    (scalarLocalization R s).mapDerivedCategoryFactors.app P ≪≫
      DerivedCategory.Q.mapIso ec ≪≫
      (U.mapDerivedCategoryFactors.app ((m.E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
      U.mapDerivedCategory.mapIso (asIso (m.ε.app P)).symm
  exact (U.mapDerivedCategory.map_isZero hz).of_iso d

private noncomputable def cech_slice_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))]
    {U V : C} (a : V ⟶ U) (r : ℕ) (g : Fin r → O.obj.obj (op U)) :
    (ringedKoszulDerivedOverMap O a).obj (DerivedCategory.Q.obj
      (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (g i))).1) ≅
    DerivedCategory.Q.obj (ringedExtendedCech (O.over V) r
      (fun i ↦ ringedSliceSection O V (O.obj.map a.op (g i)))).1 := by
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj
        (((Over.map a).sheafPushforwardContinuous CommRingCat
          (J.over V) (J.over U)).obj (O.over U)))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V))))
  let R := SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) a
  have h := augmentedCechRestriction_of_factors
    (J := J.over V) (K := J.over U) (Over.map a) (O.over U)
    (genericFactorRestriction (J := J.over V) (K := J.over U) (Over.map a) (O.over U))
    r (fun i ↦ ringedSliceSection O U (g i))
  have he := Arrow.leftFunc.mapIso (derivedArrowRestriction.{w} R
    (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (g i))).2 ≪≫
      DerivedCategory.Q.mapArrow.mapIso h.some)
  have hg : (fun i ↦ LocalizationRHom.restrictedSection (K := J.over V)
      (Over.map a) (O.over U) (ringedSliceSection O U (g i))) =
      (fun i ↦ ringedSliceSection O V (O.obj.map a.op (g i))) := by
    funext i
    apply Subtype.ext
    funext W
    change O.obj.map (W.unop.hom ≫ a).op (g i) =
      O.obj.map W.unop.hom.op (O.obj.map a.op (g i))
    rw [op_comp, O.obj.map_comp]
    rfl
  change (ringedKoszulDerivedOverMap O a).obj (DerivedCategory.Q.obj
      (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (g i))).1) ≅
    DerivedCategory.Q.obj (ringedExtendedCech (O.over V) r
      (fun i ↦ LocalizationRHom.restrictedSection (K := J.over V)
        (Over.map a) (O.over U) (ringedSliceSection O U (g i)))).1 at he
  rw [hg] at he
  exact he

private theorem ideal_section_local_span
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (U : C) (r : ℕ) (g : Fin r → O.obj.obj (op U))
    (hgen : IsRingedIdealGeneratingList O I ι U r g)
    (V : C) (a : V ⟶ U) (x : I.val.obj (op V)) :
    ∀ T : Over V, ∃ S : Sieve T, S ∈ (J.over V) T ∧
      ∀ (W : Over V) (b : W ⟶ T), S b →
        (ringedSliceSection O V (ι.val.app (op V) x)).val (op W) ∈
          Ideal.span (Set.range (fun i ↦
            (ringedSliceSection O V (O.obj.map a.op (g i))).val (op W))) := by
  intro T
  obtain ⟨S, hS, hs⟩ := exists_cover_mem_span_generatingList O I ι U r g hgen
    T.left (T.hom ≫ a) (fun _ : PUnit.{u + 1} ↦ I.val.map T.hom.op x)
  refine ⟨(Sieve.overEquiv T).symm S, J.overEquiv_symm_mem_over T S hS, ?_⟩
  intro W b hb
  have h := hs W.left b.left hb PUnit.unit
  have hn := PresheafOfModules.naturality_apply ι.val W.hom.op x
  change ι.val.app (op W.left) (I.val.map W.hom.op x) =
    O.obj.map W.hom.op (ι.val.app (op V) x) at hn
  change O.obj.map W.hom.op (ι.val.app (op V) x) ∈ _
  rw [← hn]
  have hb' : b.left ≫ T.hom = W.hom := Over.w b
  change ι.val.app (op W.left) (I.val.map b.left.op (I.val.map T.hom.op x)) ∈
    Ideal.span (Set.range (fun i ↦ O.obj.map (b.left ≫ T.hom ≫ a).op (g i))) at h
  rw [← I.val.map_comp_apply, ← op_comp, hb', ← Category.assoc, hb'] at h
  have hg : (fun i ↦ O.obj.map W.hom.op (O.obj.map a.op (g i))) =
      (fun i ↦ O.obj.map (W.hom ≫ a).op (g i)) := by
    funext i
    change (O.obj.map a.op ≫ O.obj.map W.hom.op) (g i) = _
    rw [← O.obj.map_comp, ← op_comp]
  change ι.val.app (op W.left) (I.val.map W.hom.op x) ∈
    Ideal.span (Set.range (fun i ↦ O.obj.map W.hom.op (O.obj.map a.op (g i))))
  rw [hg]
  exact h

private theorem cech_orthogonal_on_slice
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (U : C) (r : ℕ) (g : Fin r → O.obj.obj (op U))
    (hgen : IsRingedIdealGeneratingList O I ι U r g)
    (V : C) (a : V ⟶ U) (A : ringedSiteDerived (O.over V))
    (hA : ringedIdealLocalizationTriangulated O I ι V A) (n : ℤ) :
    Subsingleton (((ringedKoszulDerivedOverMap O a).obj (DerivedCategory.Q.obj
      (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (g i))).1)) ⟶ A⟦n⟧) := by
  classical
  let K := (ringedKoszulDerivedOverMap O a).obj (DerivedCategory.Q.obj
    (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (g i))).1)
  let P := (ObjectProperty.shiftClosure
    (fun X : ringedSiteDerived (O.over V) ↦ X = K) ℤ).rightOrthogonal
  have hP : P A := hA P inferInstance inferInstance (by
    intro M x hx
    let s := ringedSliceSection O V (ι.val.app (op V) x)
    let F := scalarLocalization (O.over V) s
    let := (scalarLocalization_exact (O.over V) s).1
    let := (scalarLocalization_exact (O.over V) s).2.1
    let := (scalarLocalization_exact (O.over V) s).2.2
    have hi : IsIso ((scalarLocalizationUnit (O.over V) s).app M) :=
      localization_unit_isIso (O.over V) s M (by
        rintro ⟨W⟩
        exact hx W.left W.hom)
    have hz : IsZero (F.mapDerivedCategory.obj K) :=
      (localized_cech_zero (O.over V) r
        (fun i ↦ ringedSliceSection O V (O.obj.map a.op (g i))) s
        (ideal_section_local_span O I ι U r g hgen V a x)).of_iso
          (F.mapDerivedCategory.mapIso (cech_slice_iso O a r g))
    exact exact_localization_orthogonal F (scalarLocalizationUnit (O.over V) s) K hz M)
  have hn : P (A⟦n⟧) := P.le_shift n A hP
  have hK : ObjectProperty.shiftClosure (fun X : ringedSiteDerived (O.over V) ↦ X = K) ℤ K :=
    ObjectProperty.le_shiftClosure _ K rfl
  exact ⟨fun f g ↦ (hn f hK).trans (hn g hK).symm⟩

private noncomputable def iterated_modules
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (X : Over U) :
    SheafOfModules.{u} ((R.over U).over X) ≌ SheafOfModules.{u} (R.over X.left) :=
  (SheafOfModules.pushforwardPushforwardEquivalence X.iteratedSliceEquiv
    (S := (R.over U).over X) (R := R.over X.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.obj.map_id _) (by ext : 2; exact R.obj.map_id _)).symm

private instance iterated_modules_additive
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (X : Over U) :
    (iterated_modules R U X).functor.Additive := by
  constructor
  intro A B f g
  ext Y x
  rfl

private noncomputable def iterated_derived_restriction
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))]
    (U : C) (X : Over U) :
    let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
    letI : ∀ Y : Over U, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)).over Y)) :=
        fun _ ↦ HasDerivedCategory.standard _
    letI := HasDerivedCategory.standard (SheafOfModules.{u} ((R.over U).over X))
    ringedDerivedRestrictionGeneral.{u, u, u, u, w, u + 1} (R.over U) X ⋙
      (iterated_modules R U X).functor.mapDerivedCategory ≅
        ringedKoszulDerivedOverMap O X.hom := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  letI : ∀ Y : Over U, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)).over Y)) :=
    fun _ ↦ HasDerivedCategory.standard _
  letI := HasDerivedCategory.standard (SheafOfModules.{u} ((R.over U).over X))
  let F := SheafOfModules.overFunctor.{u} (R.over U) X
  let G := (iterated_modules R U X).functor
  letI : G.Additive := iterated_modules_additive R U X
  letI : F.Additive := SheafOfModules.sitePerfectOverFunctor_additive _ _
  letI : PreservesFiniteLimits F := (SheafOfModules.overFunctor_exact_ofUniverses _ _).1
  letI : PreservesFiniteColimits F := (SheafOfModules.overFunctor_exact_ofUniverses _ _).2
  let e : F ⋙ G ≅ SheafOfModules.overMap.{u} R X.hom :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  exact (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso e

private theorem sheafify_zero_of_local_subsingleton
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (P : PresheafOfModules.{u} R.obj)
    (h : ∀ X : C, ∃ S : Sieve X, S ∈ J X ∧ ∀ (Y : C) (a : Y ⟶ X), S a →
      Subsingleton (P.obj (op Y))) :
    IsZero ((PresheafOfModules.sheafification.{u} (𝟙 R.obj)).obj P) := by
  classical
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)
  let A := (PresheafOfModules.sheafification.{u} (𝟙 R.obj)).obj P
  let η := adj.unit.app P
  have hη : η = 0 := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨S, hS, hs⟩ := h X.unop
    apply A.isSheaf.isSeparated X.unop S hS
    intro Y a ha
    have hzero : P.map a.op x = 0 := (hs Y a ha).elim _ _
    have hn := PresheafOfModules.naturality_apply η a.op x
    change η.app (op Y) (P.map a.op x) = A.val.map a.op (η.app X x) at hn
    change A.val.map a.op (η.app X x) = A.val.map a.op 0
    rw [← hn, hzero]
    exact ((η.app (op Y)).hom.map_zero).trans ((A.val.map a.op).hom.map_zero).symm
  apply (IsZero.iff_id_eq_zero A).2
  apply (adj.homEquiv P A).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  exact hη

private noncomputable def overMap_composition
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))]
    {U V W : C} (a : V ⟶ U) (b : W ⟶ V) :
    ringedKoszulDerivedOverMap O a ⋙ ringedKoszulDerivedOverMap O b ≅
      ringedKoszulDerivedOverMap O (b ≫ a) := by
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let F := SheafOfModules.overMap.{u} R a
  let G := SheafOfModules.overMap.{u} R b
  letI : F.Additive := SheafOfModules.sitePerfectOverMap_additive _ _
  letI : G.Additive := SheafOfModules.sitePerfectOverMap_additive _ _
  letI : PreservesFiniteLimits F := (SheafOfModules.overMap_exact_ofUniverses _ _).1
  letI : PreservesFiniteColimits F := (SheafOfModules.overMap_exact_ofUniverses _ _).2
  letI : PreservesFiniteLimits G := (SheafOfModules.overMap_exact_ofUniverses _ _).1
  letI : PreservesFiniteColimits G := (SheafOfModules.overMap_exact_ofUniverses _ _).2
  let e : F ⋙ G ≅ SheafOfModules.overMap.{u} R (b ≫ a) :=
    SheafOfModules.sitePerfectOverMapComp R a b
  exact (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso e

private noncomputable def homology_sheafification_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (H : CochainComplex (SheafOfModules.{u} R) ℤ) (m : ℤ) :
    (PresheafOfModules.sheafification.{u} (𝟙 R.obj)).obj
      ((((SheafOfModules.forget R).mapHomologicalComplex (.up ℤ)).obj H).homology m) ≅
        H.homology m := by
  let sh := PresheafOfModules.sheafification.{u} (𝟙 R.obj)
  have : sh.Additive :=
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).left_adjoint_additive
  let F := (SheafOfModules.forget R).mapHomologicalComplex (.up ℤ)
  let e : SheafOfModules.forget R ⋙ sh ≅ 𝟭 _ :=
    asIso (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).counit
  let c := (Functor.mapHomologicalComplexCompIso
    (F := SheafOfModules.forget R) (G := sh) (Iso.refl _) (.up ℤ)) ≪≫
    NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} R) (.up ℤ)
  exact ((F.obj H).sc m).mapHomologyIso sh |>.symm.trans
    (HomologicalComplex.homologyMapIso (c.app H) m)

private theorem local_derived_hom_vanishing
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))]
    (U : C) (K E : ringedSiteDerived (O.over U))
    (h : ∀ X : Over U, ∃ S : Sieve X, S ∈ (J.over U) X ∧
      ∀ (Y : Over U) (a : Y ⟶ X), S a → ∀ n : ℤ,
        Subsingleton (((ringedKoszulDerivedOverMap O Y.hom).obj K) ⟶
          ((ringedKoszulDerivedOverMap O Y.hom).obj E)⟦n⟧)) :
    ∀ n : ℤ, Subsingleton (K ⟶ E⟦n⟧) := by
  classical
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let R := R₀.over U
  let A := SheafOfModules.{u} R
  let : ∀ X : Over U, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (R.over X)) := fun _ ↦ HasDerivedCategory.standard _
  let : IsGrothendieckAbelian.{u} A :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
      (J.over U) (O.over U)).1
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let L := Q.objPreimage K
  let k : Q.obj L ≅ K := Q.objObjPreimageIso K
  let M := Q.objPreimage E
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} A).obj M
  let η := (CochainComplex.toKInjectiveResolution.{u} A).app M
  have : QuasiIso η := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app A M).2
  have : I.IsKInjective := CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj A M
  let i : Q.obj I ≅ E := (asIso (Q.map η)).symm ≪≫ Q.objObjPreimageIso E
  let H := homComplex (R := O.over U) L I
  let P := ((SheafOfModules.forget R).mapHomologicalComplex (.up ℤ)).obj H
  have hP (m : ℤ) : IsZero
      ((PresheafOfModules.sheafification.{u} (𝟙 R.obj)).obj (P.homology m)) := by
    apply sheafify_zero_of_local_subsingleton
    intro X
    obtain ⟨S, hS, hs⟩ := h X
    refine ⟨S, hS, ?_⟩
    intro Y a ha
    let F := ringedDerivedRestrictionGeneral.{u, u, u, u, w, u + 1} R Y
    let res := (SheafOfModules.overFunctor.{u} R Y).mapHomologicalComplex (.up ℤ)
    let ev := PresheafOfModules.evaluation R.obj (op Y) ⋙
      forget₂ (ModuleCat.{u} (R.obj.obj (op Y))) AddCommGrpCat
    let eh := (P.sc m).mapHomologyIso ev
    let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)).over Y)) :=
      HasDerivedCategory.standard _
    obtain ⟨e, _, _⟩ := homComplex_sections_derived_naturalityOfUniverses.{u, u, u, u + 1}
      (O.over U) Y (𝟙 I) (𝟙 L) m
    have hfl : F.obj (Q.obj L) ≅ DerivedCategory.Q.obj (res.obj L) := by
      let := (SheafOfModules.overFunctor_exact_ofUniverses R Y).1
      let := (SheafOfModules.overFunctor_exact_ofUniverses R Y).2
      exact (SheafOfModules.overFunctor.{u} R Y).mapDerivedCategoryFactors.app L
    have hfi : F.obj (Q.obj I) ≅ DerivedCategory.Q.obj (res.obj I) := by
      let := (SheafOfModules.overFunctor_exact_ofUniverses R Y).1
      let := (SheafOfModules.overFunctor_exact_ofUniverses R Y).2
      exact (SheafOfModules.overFunctor.{u} R Y).mapDerivedCategoryFactors.app I
    let ek := hfl.symm ≪≫ F.mapIso k
    let ei := (DerivedCategory.Q.commShiftIso m).app (res.obj I) ≪≫
      (shiftFunctor _ m).mapIso (hfi.symm ≪≫ F.mapIso i)
    let G := (iterated_modules R₀ U Y).functor.mapDerivedCategory
    let c := iterated_derived_restriction O U Y
    have hh := hs Y a ha m
    refine ⟨fun x y ↦ ?_⟩
    apply eh.symm.addCommGroupIsoToAddEquiv.injective
    apply e.injective
    apply (Iso.homCongr ek ei).injective
    apply G.map_injective
    apply (Iso.homCongr (c.app K)
      ((G.commShiftIso m).app (F.obj E) ≪≫
        (shiftFunctor _ m).mapIso (c.app E))).injective
    exact hh.elim _ _
  have hzH : IsZero (Q.obj H) := by
    apply (DerivedCategory.isZero_iff _).2
    intro m
    exact (hP m).of_iso
      (homology_sheafification_iso R H m ≪≫
        (DerivedCategory.homologyFunctorFactors A m).symm.app H).symm
  obtain ⟨er⟩ := derivedInternalHomOfUniverses_obj_iso.{u, u, u, w}
    (J.over U) (O.over U) K E L I k i
  have hz : IsZero ((derivedInternalHomOfUniverses.{u, u, u, w}
      (J.over U) (O.over U)).obj (op K, E)) := hzH.of_iso er
  let Hf := (Functor.curry.obj
    (derivedInternalHomOfUniverses.{u, u, u, w} (J.over U) (O.over U))).obj (op K)
  let : Hf.CommShift ℤ :=
    RingedHomUniverses.homCommShift.{u, u, u, w} (J.over U) (O.over U) K
  let Γ := ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w}
    (J.over U) (O.over U)
  have : Γ.Additive := by
    let := HasDerivedCategory.standard AddCommGrpCat.{u}
    dsimp only [Γ, ringedSiteZerothHypercohomologyOfUniverses]
    infer_instance
  obtain ⟨eg, _⟩ := rhom_global_sectionsOfUniverses.{u, u, u, w}
    (J.over U) (O.over U)
  intro n
  have hzn : IsZero (Hf.obj (E⟦n⟧)) :=
    ((shiftFunctor _ n).map_isZero hz).of_iso ((Hf.commShiftIso n).app E)
  have hΓ := Γ.map_isZero hzn
  have hs := AddCommGrpCat.isZero_iff_subsingleton.mp hΓ
  exact ⟨fun f g ↦ (eg (op K, E⟦n⟧)).symm.injective (hs.elim _ _)⟩

/-- An extended Cech object has no shifted derived maps to an object locally in the
finite triangulated localization class, on every slice.
Source: Stacks Project, dualizing.tex, Tag 0A6R; sites-cohomology.tex,
Tags 0A94, 0A95, 08JA, 08JB and 08JC.
(blueprint: lem-weil-pbc-augmented-cech-local-orthogonality).

Proof:
1. Restrict the Cech complex to an arbitrary slice. Finite local generation implies
   that each ideal section locally belongs to the span of the restricted generators.
   The stated Cech localization acyclicity therefore annihilates the source after
   derived extension to the ring sheaf localized at that section.
2. Identify scalar localization with extension followed by restriction of scalars.
   K-flatness of the Cech complex compares its derived extension with the termwise
   extension. Exactness then shows that derived scalar localization kills the source.
3. If the section acts invertibly on a module, inverse powers give an inverse to the
   sequential-colimit localization unit. The derived unit is consequently invertible
   on this module in degree zero. Naturality of the unit kills every map from every
   shift of the localized-zero Cech source to that module.
4. The right orthogonal of the shift closure of the source is strictly full
   triangulated. Step 3 puts all defining module generators in it; the intersection
   definition puts the entire localization class in it.
5. Choose a representative and use the proved K-injective local-RHom section
   equivalence. The covering sieves supplied below every arrow make the values of
   the resolved Hom cohomology presheaf locally subsingleton, by step 4. Sheaf
   separation makes its sheafification zero; the proved sheafification comparison
   identifies this with every cohomology object of derived internal Hom, so the
   derived zero criterion gives derived internal Hom equal to zero.
6. The proved zeroth-hypercohomology comparison identifies all shifted derived
   morphisms with the zero internal-Hom object. Composition of restrictions transports
   the local assertions to every initial slice. The proof also covers the empty
   generating list and zero and unit ideals. -/
theorem ringed_augmented_cech_local_orthogonality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (U : C) (r : ℕ) (g : Fin r → O.obj.obj (op U))
    (hgen : IsRingedIdealGeneratingList O I ι U r g)
    (E : ringedSiteDerived (O.over U))
    (hlocal : ∀ (V : C) (a : V ⟶ U), ∃ S : Sieve V, S ∈ J V ∧
      ∀ (W : C) (b : W ⟶ V), S b →
        ringedIdealLocalizationTriangulated O I ι W
          ((ringedKoszulDerivedOverMap O (b ≫ a)).obj E)) :
    ∀ (V : C) (a : V ⟶ U) (n : ℤ),
      Subsingleton
        (((ringedKoszulDerivedOverMap O a).obj
            (DerivedCategory.Q.obj
              (ringedExtendedCech (O.over U) r
                (fun i ↦ ringedSliceSection O U (g i))).1)) ⟶
          ((ringedKoszulDerivedOverMap O a).obj E)⟦n⟧) := by
  classical
  let K := DerivedCategory.Q.obj
    (ringedExtendedCech (O.over U) r (fun i ↦ ringedSliceSection O U (g i))).1
  intro V a n
  apply local_derived_hom_vanishing O V
  intro X
  obtain ⟨S, hS, hs⟩ := hlocal X.left (X.hom ≫ a)
  refine ⟨(Sieve.overEquiv X).symm S, J.overEquiv_symm_mem_over X S hS, ?_⟩
  intro Y b hb m
  have hA := hs Y.left b.left hb
  have hc : b.left ≫ (X.hom ≫ a) = Y.hom ≫ a := by
    rw [← Category.assoc, Over.w b]
  rw [hc] at hA
  have hh := cech_orthogonal_on_slice O I ι U r g hgen
    Y.left (Y.hom ≫ a) _ hA m
  let c := overMap_composition O a Y.hom
  let eK := c.app K
  let eE := (shiftFunctor _ m).mapIso (c.app E)
  exact ⟨fun f g ↦ (Iso.homCongr eK eE).injective (hh.elim _ _)⟩

end CategoryTheory
