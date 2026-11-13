/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardContinuity
import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # The evaluation identification for finite locally free internal modules -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Derived maps from P[0] are derived sections of internal Hom from P.
Source: Stacks Project, Tag 08JJ; Hemo--Richarz--Scholbach, Lemma 5.3(2), evaluation. -/
theorem condensed_finite_free_hom_evaluation
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : IsLocallyFree (condensedRingObj Λ X) P)
    (n : ℤ) : Nonempty
      (DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
          preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor _ 0).obj P)) ≅
        (Mod.ihom P).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⋙
          (condensedModuleSections Λ X).rightDerivedFunctor ⋙
            DerivedCategory.homologyFunctor _ n) := by
  -- Use ordinary internal-module evaluation directly; no ringed-site transport is needed.
  let R := condensedRingObj Λ X
  let F := Mod.ihom P
  let Γ := condensedModuleSections Λ X
  have : PreservesFiniteLimits (Mod.tensorLeft P) :=
    condensed_locally_free_tensor_preservesFiniteLimits R P hP
  have : (Mod.tensorLeft P).Additive := (Mod.ihomAdjunction P).left_adjoint_additive
  have : PreservesLimitsOfSize.{u + 1, u + 1} F :=
    (Mod.ihomAdjunction P).rightAdjoint_preservesLimits
  have : F.PreservesKInjectiveComplexes :=
    (Mod.ihomAdjunction P).preservesKInjectiveComplexes
  have : PreservesColimitsOfSize.{u + 1, u + 1} F :=
    condensed_locally_free_ihom_preservesColimits R P hP
  obtain ⟨e⟩ := condensed_internal_hom_sections X Λ P
  obtain ⟨d⟩ := CategoryTheory.derived_coyoneda_evaluation P n
  let c : (preadditiveCoyoneda.obj (op P)).rightDerivedFunctor ≅
      F.mapDerivedCategory ⋙ Γ.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompIso' F Γ e).symm ≪≫
      Functor.isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory _
  exact ⟨Functor.isoWhiskerLeft DerivedCategory.Q d ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Q
      (Functor.isoWhiskerRight c (DerivedCategory.homologyFunctor _ n)) ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors
      (Γ.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ n)⟩

end AlgebraicGeometry.ProEtale
