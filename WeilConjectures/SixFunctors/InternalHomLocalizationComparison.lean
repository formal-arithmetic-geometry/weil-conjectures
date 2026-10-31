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
attribute [local instance] localizationTensor_additive

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
attribute [local irreducible] localizationComplexScalar

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
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
attribute [local irreducible] localizationHomComplex

omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
omit [∀ T : Sheaf J CommRingCat.{max c v r},
  HasDerivedCategory.{w} (scalarModules J T)] in
include M in
end CategoryTheory
