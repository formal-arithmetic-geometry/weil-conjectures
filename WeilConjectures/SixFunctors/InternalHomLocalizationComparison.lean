/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Localization.Adjunction
import all WeilConjectures.CategoryTheory.ProperBaseChange.LocalizationInverseImageCoherence
import WeilConjectures.CategoryTheory.SmoothPurity.ComplexColimitHomotopyColimit
import all WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import all WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
import all WeilConjectures.Algebra.Homology.ScalarHomCancellation.ScalarHomTensorCancellation
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteLocalization

/-! # Internal Hom and localization under sequential continuity

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62,
conditional internal-sheaf localization argument (not the global Hom assertion);
Stacks Project, Tags 03CY, 03DB, 03ET, 06YY, 07A6 and 08J9
(blueprint: lem-sfb-internal-hom-localization-comparison).

All derived operations are the recorded, evaluation-normalized operations.
Sequential colimits are formed in complexes of module sheaves, before applying Q.
The functorial Hom representatives are the same ones as in the recorded internal Hom.
Exact filtered colimits are supplied by the Grothendieck-abelian module-sheaf theorem
on this small site; no independent exactness witness or stronger coefficient condition is needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures SheafOfModules
open CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory
  derivedInternalHomOfUniverses

namespace CategoryTheory
namespace LocalizationHomProof

universe u₁ v₁ u₂ v₂
variable {A : Type u₁} [Category.{v₁} A] {H : Aᵒᵖ × A ⥤ A}
  (S : CoefficientClosedStructure H)

universe w₁

end LocalizationHomProof

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]

variable {J}
  (M : ScalarHomModels.{c, v, r, w} J)
  {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)

attribute [local irreducible] ScalarHomCancellation.cancellationRestrictSheafifyIso
  ScalarHomCancellation.cancellationRestrictSheafifyHom

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})] in
omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
variable (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J CommRingCat.{max c v r}]
  (s : (R.obj ⋙ forget CommRingCat).sections)

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationTensor_additive : (scalarLocalization R s).Additive :=
  (scalarLocalization_exact R s).1

attribute [local instance] localizationTensor_additive

private def localizationRestrictedTensorPresheafIso (N : scalarModules J R) :
    N.val ⊗ ((scalarRestriction a).obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ≅
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a).hom).obj
        (changeOfRingsPresheaf a N) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let ρ := (a.hom.app V).hom
    change ModuleCat.of (R.obj.obj V) (TensorProduct (R.obj.obj V) (N.val.obj V)
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) (S.obj.obj V)))) ≅
      (ModuleCat.restrictScalars ρ).obj
        ((ModuleCat.extendScalars ρ).obj (N.val.obj V))
    exact (TensorProduct.comm (R.obj.obj V) (N.val.obj V)
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V)
        (S.obj.obj V)))).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x b =>
        change S.obj.map f b ⊗ₜ[R.obj.obj W, (a.hom.app W).hom] N.val.map f x =
          changeOfRingsMap a N f (b ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)
        exact (Classical.choose_spec (exists_changeOfRingsMap a N f) b x).symm

private def localizationRestrictedTensorIso (N : scalarModules J R) :
    (SheafOfModules.monoidalCategory R).tensorObj N
      ((scalarRestriction a).obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) ≅
      (scalarRestriction a).obj (changeOfRings a N) := by
  let _ := SheafOfModules.monoidalCategory R
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  exact tensorObjIsoSheafification N _ ≪≫
    F.mapIso (localizationRestrictedTensorPresheafIso.{c, v, r} a N) ≪≫
      ScalarHomCancellation.cancellationRestrictSheafifyIso
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)
        (changeOfRingsPresheaf a N)

private theorem localizationRestrictionSheafification_unit
    {A B : Sheaf J RingCat.{max c v r}} (a₀ : A ⟶ B)
    (P : PresheafOfModules.{max c v r} B.obj) (V : Cᵒᵖ) (x : P.obj V) :
    (ScalarHomCancellation.cancellationRestrictSheafifyIso a₀ P).hom.val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 A.obj)).unit.app
        ((PresheafOfModules.restrictScalars a₀.hom).obj P)).app V x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P).app V x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars a₀.hom).obj P)
    (F := (restrictScalars a₀).obj
      ((PresheafOfModules.sheafification (𝟙 B.obj)).obj P)) (𝟙 A.obj)).apply_symm_apply
      ((PresheafOfModules.restrictScalars a₀.hom).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P))
  have h' := congrArg ((PresheafOfModules.toPresheaf A.obj).map) h
  rw [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def] at h'
  have hx := congrArg (fun k ↦ k.app V x) h'
  unfold ScalarHomCancellation.cancellationRestrictSheafifyIso
  change (ScalarHomCancellation.cancellationRestrictSheafifyHom a₀ P).val.app V
    (((PresheafOfModules.sheafificationAdjunction (𝟙 A.obj)).unit.app
      ((PresheafOfModules.restrictScalars a₀.hom).obj P)).app V x) = _
  unfold ScalarHomCancellation.cancellationRestrictSheafifyHom
  exact hx

private theorem localizationRestrictedTensorIso_pure
    (N : scalarModules J R) (V : Cᵒᵖ) (x : N.val.obj V) (b : S.obj.obj V) :
    (localizationRestrictedTensorIso.{c, v, r} a N).hom.val.app V
      (ScalarHomOrdinary.pure R N ((scalarRestriction a).obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) V x b) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.app
          (changeOfRingsPresheaf a N)).app V
            (b ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x) := by
  let B := (scalarRestriction a).obj (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let eP := localizationRestrictedTensorPresheafIso.{c, v, r} a N
  let c := ScalarHomCancellation.cancellationRestrictSheafifyIso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) (changeOfRingsPresheaf a N)
  have he : (tensorObjIsoSheafification N B).inv ≫
      (localizationRestrictedTensorIso.{c, v, r} a N).hom = F.map eP.hom ≫ c.hom := by
    dsimp only [localizationRestrictedTensorIso, Iso.trans_hom, Functor.mapIso_hom]
    change (tensorObjIsoSheafification N B).inv ≫
      (tensorObjIsoSheafification N B).hom ≫ F.map eP.hom ≫ c.hom = _
    rw [Iso.inv_hom_id_assoc]
  have hn := congrArg (fun k ↦ k.app V (x ⊗ₜ[R.obj.obj V] b))
    (adj.unit.naturality eP.hom)
  have hh := congrArg (fun k ↦ k.val.app V
    ((adj.unit.app (N.val ⊗ B.val)).app V (x ⊗ₜ[R.obj.obj V] b))) he
  change (localizationRestrictedTensorIso.{c, v, r} a N).hom.val.app V
    (ScalarHomOrdinary.pure R N B V x b) = _ at hh
  rw [hh]
  change c.hom.val.app V ((F.map eP.hom).val.app V
    ((adj.unit.app (N.val ⊗ B.val)).app V (x ⊗ₜ[R.obj.obj V] b))) = _
  change (adj.unit.app ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a).hom).obj
        (changeOfRingsPresheaf a N))).app V (eP.hom.app V (x ⊗ₜ[R.obj.obj V] b)) =
      (F.map eP.hom).val.app V
        ((adj.unit.app (N.val ⊗ B.val)).app V (x ⊗ₜ[R.obj.obj V] b)) at hn
  refine (congrArg (c.hom.val.app V) hn.symm).trans ?_
  exact localizationRestrictionSheafification_unit.{c, v, r}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map a) (changeOfRingsPresheaf a N) V
    (b ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)

private def localizationUnderlyingIso (N : scalarModules J R) :
    (scalarLocalization R s).obj N ≅
      (scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
        ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension.obj N) := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let _ := SheafOfModules.monoidalCategory R
  let e := Classical.choose (ringedLocalizationRing_moduleComparisonOfUniverses R s)
  exact (ScalarHomOrdinary.tensorIsoSite R N
      (ringedSectionLocalizationOfUniverses R s)).symm ≪≫
    (MonoidalCategory.tensorIso (Iso.refl N) e.symm) ≪≫
      localizationRestrictedTensorIso.{c, v, r} a N ≪≫
        (scalarRestriction a).mapIso (eqToIso ((M.scalar a).extension_obj N)).symm

private theorem localizationUnderlyingIso_unit (N : scalarModules J R) :
    (scalarLocalizationUnit R s).app N ≫ (localizationUnderlyingIso M R s N).hom =
      (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).ordinaryAdjunction.unit.app N := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  let U := scalarRestriction a
  let e := Classical.choose (ringedLocalizationRing_moduleComparisonOfUniverses R s)
  have he := Classical.choose_spec (ringedLocalizationRing_moduleComparisonOfUniverses R s)
  apply (cancel_mono (U.map (eqToHom ((M.scalar a).extension_obj N)))).mp
  dsimp only [localizationUnderlyingIso, U, a, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom,
    eqToIso.hom, eqToIso.inv]
  simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl,
    Functor.map_id, Category.comp_id]
  apply SheafOfModules.hom_ext
  ext V x
  have he₁ : e.hom.val.app V
      (1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) =
      (ringedSectionLocalizationUnitOfUniverses R s).val.app V (1 : R.obj.obj V) := by
    have h := he V (1 : ringedSectionLocalizationCarrierOfUniverses R s V)
    simp only [map_one] at h
    change e.hom.val.app V
      (1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
          (ringedSectionLocalizationPresheafOfUniverses R s)).app V
            ((1 : R.obj.obj V) • (1 : ringedSectionLocalizationCarrierOfUniverses R s V))
    rw [one_smul]
    exact h
  have he₁' : e.inv.val.app V
      ((ringedSectionLocalizationUnitOfUniverses R s).val.app V (1 : R.obj.obj V)) =
      (1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) := by
    rw [← he₁]
    exact congrArg (fun f ↦ f.val.app V
      (1 : (ringedLocalizationRingOfUniverses R s).obj.obj V)) e.hom_inv_id
  have hη := (Classical.choose_spec (existsUnique_scalarLocalizationUnit R s)).1 N V x
  change (((scalarLocalizationUnit R s).app N).val.app V x) =
    siteSheafTensorTmul N (ringedSectionLocalizationOfUniverses R s) V x
      ((ringedSectionLocalizationUnitOfUniverses R s).val.app V (1 : R.obj.obj V)) at hη
  change (localizationRestrictedTensorIso.{c, v, r} a N).hom.val.app V
    (((SheafOfModules.monoidalCategory R).tensorHom (𝟙 N) e.inv).val.app V
      ((ScalarHomOrdinary.tensorIsoSite R N
        (ringedSectionLocalizationOfUniverses R s)).inv.val.app V
          (((scalarLocalizationUnit R s).app N).val.app V x))) =
    (eqToHom ((M.scalar a).extension_obj N)).val.app V
      (((M.scalar a).ordinaryAdjunction.unit.app N).val.app V x)
  rw [hη, ScalarHomOrdinary.tensorIsoSite_inv_pure, ScalarHomOrdinary.pure_map]
  simp only [SheafOfModules.id_val]
  rw [he₁', localizationRestrictedTensorIso_pure.{c, v, r}, (M.scalar a).ordinaryUnit]
  simp only [PresheafOfModules.id_app, ModuleCat.id_apply,
    ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  exact congrArg (fun f ↦ f.app V
    ((1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) ⊗ₜ[R.obj.obj V,
      (a.hom.app V).hom] x))
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R s)).obj) (changeOfRingsPresheaf a N))

private theorem localizationUnderlying_scalar_isIso (N : scalarModules J R) :
    IsIso (localizationScalar R s
      ((scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
        ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension.obj N))) := by
  let i := localizationUnderlyingIso M R s N
  have : IsIso (localizationScalar R s ((scalarLocalization R s).obj N)) :=
    LocalizationSequence.colimit_scalar_isIso R s
      (LocalizationSequence.moduleSheafCocone R s N)
      (LocalizationSequence.moduleSheafCoconeIsColimit R s N)
  have h := LocalizationSequence.scalar_naturality R s i.hom
  have hi : IsIso (i.hom ≫ localizationScalar R s
      ((scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).obj
        ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension.obj N))) := by
    rw [← h]
    infer_instance
  exact (isIso_comp_left_iff i.hom _).mp hi

private theorem localizationUnderlyingIso_naturality
    {N N' : scalarModules J R} (f : N ⟶ N') :
    (scalarLocalization R s).map f ≫ (localizationUnderlyingIso M R s N').hom =
      (localizationUnderlyingIso M R s N).hom ≫
        (scalarRestriction (ringedLocalizationRingUnitOfUniverses R s)).map
          ((M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension.map f) := by
  let a := ringedLocalizationRingUnitOfUniverses R s
  have := localizationUnderlying_scalar_isIso M R s N'
  apply LocalizationSequence.colimit_hom_ext_zero R s
    (LocalizationSequence.moduleSheafCocone R s N)
    (LocalizationSequence.moduleSheafCoconeIsColimit R s N)
  rw [LocalizationSequence.moduleSheafCocone_zero]
  calc
    _ = f ≫ (scalarLocalizationUnit R s).app N' ≫
        (localizationUnderlyingIso M R s N').hom := by
      rw [← Category.assoc, ← (scalarLocalizationUnit R s).naturality f,
        Category.assoc, Functor.id_map]
    _ = f ≫ (M.scalar a).ordinaryAdjunction.unit.app N' := by
      rw [localizationUnderlyingIso_unit]
    _ = (M.scalar a).ordinaryAdjunction.unit.app N ≫
        (scalarRestriction a).map ((M.scalar a).extension.map f) :=
      (M.scalar a).ordinaryAdjunction.unit.naturality f
    _ = _ := by rw [← localizationUnderlyingIso_unit M R s N, Category.assoc]

private def localizationUnderlyingNatIso :
    scalarLocalization R s ≅
      (M.scalar (ringedLocalizationRingUnitOfUniverses R s)).extension ⋙
        scalarRestriction (ringedLocalizationRingUnitOfUniverses R s) :=
  NatIso.ofComponents (localizationUnderlyingIso M R s)
    (fun f ↦ localizationUnderlyingIso_naturality M R s f)

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private def localizationComplexScalar
    (P : CochainComplex (scalarModules J R) ℤ) : P ⟶ P where
  f i := localizationScalar R s (P.X i)
  comm' i j _ := LocalizationSequence.scalar_naturality R s (P.d i j)

attribute [local irreducible] localizationComplexScalar

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
private theorem localizationModuleLeg_naturality
    {N N' : scalarModules J R} (f : N ⟶ N') (n : ℕ) :
    f ≫ (LocalizationSequence.moduleSheafCocone R s N').ι.app n =
      (LocalizationSequence.moduleSheafCocone R s N).ι.app n ≫
        (scalarLocalization R s).map f := by
  have : IsIso (localizationScalar R s ((scalarLocalization R s).obj N')) :=
    LocalizationSequence.colimit_scalar_isIso R s
      (LocalizationSequence.moduleSheafCocone R s N')
      (LocalizationSequence.moduleSheafCoconeIsColimit R s N')
  have hstep (T : scalarModules J R) (k : ℕ) :
      localizationScalar R s T ≫
        (LocalizationSequence.moduleSheafCocone R s T).ι.app (k + 1) =
      (LocalizationSequence.moduleSheafCocone R s T).ι.app k := by
    simpa only [Functor.ofSequence_map_homOfLE_succ] using
      (LocalizationSequence.moduleSheafCocone R s T).w (homOfLE (Nat.le_succ k))
  induction n with
  | zero =>
      rw [LocalizationSequence.moduleSheafCocone_zero,
        LocalizationSequence.moduleSheafCocone_zero]
      exact (scalarLocalizationUnit R s).naturality f
  | succ n ih =>
      apply (cancel_mono
        (localizationScalar R s ((scalarLocalization R s).obj N'))).mp
      calc
        _ = f ≫ localizationScalar R s N' ≫
            (LocalizationSequence.moduleSheafCocone R s N').ι.app (n + 1) := by
          rw [Category.assoc,
            ← LocalizationSequence.scalar_naturality, ← Category.assoc]
        _ = f ≫ (LocalizationSequence.moduleSheafCocone R s N').ι.app n := by
          rw [hstep]
        _ = (LocalizationSequence.moduleSheafCocone R s N).ι.app n ≫
            (scalarLocalization R s).map f := ih
        _ = localizationScalar R s N ≫
            (LocalizationSequence.moduleSheafCocone R s N).ι.app (n + 1) ≫
              (scalarLocalization R s).map f := by rw [← hstep N n, Category.assoc]
        _ = _ := by
          rw [LocalizationSequence.scalar_naturality, Category.assoc]

private def localizationComplexLeg
    (P : CochainComplex (scalarModules J R) ℤ) (n : ℕ) :
    P ⟶ ((scalarLocalization R s).mapHomologicalComplex (.up ℤ)).obj P where
  f i := (LocalizationSequence.moduleSheafCocone R s (P.X i)).ι.app n
  comm' i j _ := (localizationModuleLeg_naturality.{c, v, r} R s (P.d i j) n).symm

attribute [local irreducible] localizationComplexLeg

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
omit [HasSheafify J CommRingCat.{max c v r}] in
omit [HasSheafify J CommRingCat.{max c v r}] in
/-- Fixed functorial complex representatives of internal Hom from K. The source is
Q's chosen representative and the target uses exactly the existing K-injective functor.
Source: Stacks 08J7, 0A95; Bhatt--Scholze 6.8.12, conditional internal-sheaf version
(blueprint: lem-sfb-internal-hom-localization-comparison). -/
def localizationHomComplex (R : Sheaf J CommRingCat.{max c v r})
    (K : DerivedCategory (scalarModules J R)) :
    CochainComplex (scalarModules J R) ℤ ⥤ CochainComplex (scalarModules J R) ℤ :=
  coefficientHomResolution.{r, c, v} J R ⋙
    (homComplexFunctor (R := R)).obj (op (DerivedCategory.Q.objPreimage K))

attribute [local irreducible] localizationHomComplex

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
include M in
end CategoryTheory
