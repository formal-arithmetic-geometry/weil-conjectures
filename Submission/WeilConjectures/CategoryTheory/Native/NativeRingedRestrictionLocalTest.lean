/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.CategoryTheory.Native.NativeRingedRestrictionSlicesSupplement
public import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
public import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import Submission.WeilConjectures.Algebra.Homology.HomComplex
public import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationOfUniversesSupplement
public import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionSheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedPrincipalLocalTests
import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionDerivedHom
import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.Additive
import Submission.WeilConjectures.Algebra.Homology.HomComplex
import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
import Submission.WeilConjectures.SixFunctors.Etale.Derived.Hom
import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.Algebra.Category.Grp.Abelian
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import Submission.WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import Mathlib.Algebra.Homology.QuasiIso
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Restriction of a principal localization test
Source: Stacks 03A0, 03CH, 03DA, 03DG and 0999.
(blueprint: lem-pur-native-ringed-restriction-local-test). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxErrors 5
universe c d vc vd r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
variable {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
  {K : GrothendieckTopology C} {J : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsEquivalence] [F.IsDenseSubsite K J]
  (R : Sheaf J CommRingCat.{max c d vc vd r})
  [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [∀ U : D, HasSheafify (J.over U) AddCommGrpCat.{max c d vc vd r}]
  [∀ U : D, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [∀ U : C, HasSheafify (K.over U) AddCommGrpCat.{max c d vc vd r}]
  [∀ U : C, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [∀ U : D, HasSheafify (J.over U) CommRingCat.{max c d vc vd r}]
  [∀ U : C, HasSheafify (K.over U) CommRingCat.{max c d vc vd r}]
set_option hygiene false in
local notation "S" => restrictedCommRing.{c, d, vc, vd, r} (K := K) F R
set_option hygiene false in
local notation "Rg" => NativeRings.{max c d vc vd r, d, vd} R
set_option hygiene false in
local notation "Rs" => NativeRings.{max c d vc vd r, c, vc} S
variable [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, d, vd} R)]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, c, vc} S)]
  [∀ U : D, HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r} ((Rg).over U))]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r} ((Rs).over U))]
attribute [local instance] sliceDense globalModulesEquivalence sliceModulesEquivalence

/-- The derived localization test commutes with restriction to the equivalent slice. Compare derived
internal Hom, compare the localized module by the localization restriction isomorphism, and
compare its degree-zero derived object. The exact derived slice square compares the second Hom
argument. Compose these isomorphisms, reversing the localization isomorphism in the
contravariant argument.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0999.
(blueprint: lem-pur-native-ringed-restriction-local-test). -/
theorem localTestRestriction (U : C)
    (N : DerivedCategory (NativeModules.{max c d vc vd r, d, vd} R))
    (s : ((R.over (F.obj U)).obj ⋙ forget CommRingCat).sections) :
    let Ts := restrictModules.{max c vc, max d vd, vc, vd, r}
      (K := K.over U) (Over.post F) (R.over (F.obj U))
    letI : HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max d vd, vd}
      (R.over (F.obj U))) := inferInstanceAs
        (HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r} ((Rg).over (F.obj U))))
    letI : HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
      (restrictedCommRing.{max c vc, max d vd, vc, vd, r} (K := K.over U)
        (Over.post F) (R.over (F.obj U)))) := inferInstanceAs
        (HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r} ((Rs).over U)))
    Nonempty (Ts.mapDerivedCategory.obj
      (principalLocalTest.{d, vd, max c vc r, w} R N (F.obj U) s) ≅
        principalLocalTest.{c, vc, max d vd r, w} S
          ((restrictModules.{c, d, vc, vd, r} (K := K) F R).mapDerivedCategory.obj N) U
          (restrictedSection.{max c vc, max d vd, vc, vd, r}
            (K := K.over U) (Over.post F) (R.over (F.obj U)) s)) := by
  let : HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max d vd, vd}
    (R.over (F.obj U))) := inferInstanceAs
      (HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r} ((Rg).over (F.obj U))))
  let : HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
    (restrictedCommRing.{max c vc, max d vd, vc, vd, r} (K := K.over U)
      (Over.post F) (R.over (F.obj U)))) := inferInstanceAs
      (HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r} ((Rs).over U)))
  let : HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
    ((S).over U)) := inferInstanceAs
      (HasDerivedCategory.{w} (SheafOfModules.{max c d vc vd r} ((Rs).over U)))
  let Tg := restrictModules.{c, d, vc, vd, r} (K := K) F R
  let Ts := restrictModules.{max c vc, max d vd, vc, vd, r}
    (K := K.over U) (Over.post F) (R.over (F.obj U))
  let A := SheafOfModules.overFunctor.{max c d vc vd r} Rg (F.obj U)
  let B := SheafOfModules.overFunctor.{max c d vc vd r} Rs U
  let := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd, max c d vc vd r}
    Rg (F.obj U)).1
  let := (SheafOfModules.overFunctor_exact_ofUniverses.{d, vd, max c d vc vd r}
    Rg (F.obj U)).2
  let := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc, max c d vc vd r} Rs U).1
  let := (SheafOfModules.overFunctor_exact_ofUniverses.{c, vc, max c d vc vd r} Rs U).2
  let L := ringedSectionLocalizationOfUniverses (R.over (F.obj U)) s
  obtain ⟨α⟩ := derivedHomRestriction.{max c vc, max d vd, vc, vd, r, w, w}
    (K := K.over U) (Over.post F) (R.over (F.obj U)) (fun _ ↦ inferInstance)
      ((DerivedCategory.singleFunctor _ 0).obj L) (A.mapDerivedCategory.obj N)
  obtain ⟨β⟩ := localizationRestriction.{max c vc, max d vd, vc, vd, r}
    (K := K.over U) (Over.post F) (R.over (F.obj U)) s
  let eL := ((Ts.mapDerivedCategorySingleFunctor 0).app L) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso β
  let eN := (sliceDerivedRestrictionIso.{c, d, vc, vd, r, w} (K := K) F R U).app N
  exact ⟨α ≪≫ (derivedInternalHomOfUniverses.{max c vc, vc, max d vd r, w}
    (K.over U) ((S).over U)).mapIso (eL.symm.op.prod eN)⟩
end CategoryTheory.NativeRestriction
