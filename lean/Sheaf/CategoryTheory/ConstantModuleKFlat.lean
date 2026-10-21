/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.RingTheory.Flat.Basic
import Sheaf.CategoryTheory.ConstantModuleFlat
import Sheaf.Algebra.Homology.FlatTermKFlatFunctor
import all Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! Constant realization preserves flat-term K-flat complexes on arbitrary sites. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

namespace CategoryTheory

private theorem constantModule_colimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v)) [CommRing R] :
    PreservesColimitsOfSize.{0, 0} (commutativeSiteConstantModuleFunctor J R) := by
  let : HasSheafify J AddCommGrpCat.{max u v} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  let P := siteConstantModulePresheafGeneral (C := C) R
  have : PreservesColimitsOfSize.{0, 0} P := by
    constructor
    intro K _
    constructor
    intro D
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun _ ↦ hc)⟩
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  change PreservesColimitsOfSize.{0, 0}
    (P ⋙ PresheafOfModules.sheafification.{max u v} (realizationRingUnit J R))
  infer_instance

/-- Constant realization preserves K-flat complexes whose terms are flat.
Source: Stacks Project, Tag 0G7E
(blueprint: lem-sfb-constant-module-kflat).
Proof: constant module presheaves preserve colimits by evaluation, and module
sheafification is a left adjoint. Constant realization preserves flat objects by
the local relation criterion. Apply preservation of flat-term K-flat complexes
by additive functors preserving flat objects and integer-indexed colimits. The
categorical K-flat conclusion implies that tensoring any acyclic complex with
the realized complex is acyclic by applying it to the quasi-isomorphism 0 → Z.
This uses neither a terminal site object nor enough points. -/
theorem isKFlat_constantModule
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v)) [CommRing R] (P : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hP : P.IsKFlatForTotalTensor) (hf : ∀ i, Module.Flat R (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := realizationRing J R)
      (((commutativeSiteConstantModuleFunctor J R).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : HasSheafify J AddCommGrpCat.{max u v} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  let O := realizationRing J R
  let A := realizationModules J R
  let F := commutativeSiteConstantModuleFunctor J R
  let := SheafOfModules.isMonoidal_W_independentCoefficients O
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := SheafOfModules.tensorPreadditive O
  let := SheafOfModules.monoidalClosed_kfi (R := O)
  have : IsGrothendieckAbelian.{max u v} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses
      J O).1
  have : F.PreservesFlat := ⟨fun hM ↦ SheafOfModules.flat_to_cat O _
    (isFlatOnSite_constantModule J R _ ((ModuleCat.flat_iff_flat _).1 hM))⟩
  have : PreservesColimitsOfSize.{0, 0} F := constantModule_colimits J R
  have hp : (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat P := hP
  have hk := F.kFlat_map_of_flat_terms P hp
    (fun i ↦ (ModuleCat.flat_iff_flat _).2 (hf i))
  intro Z hZ
  let T := MonoidalCategory.tensorRight ((F.mapHomologicalComplex (.up ℤ)).obj P)
  have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hk.2 _ hz
  have htzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)

end CategoryTheory
