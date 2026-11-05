/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ClosedSupportStratumHom
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic

import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import all WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import all WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import all Mathlib.Algebra.Homology.CochainComplexPlus
import all Mathlib.Data.Int.Interval
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import all WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import all Mathlib.Algebra.Homology.TotalComplex
import all Mathlib.CategoryTheory.Abelian.Basic
import all WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import all WeilConjectures.CategoryTheory.Triangulated.Recollement
import all Mathlib.Algebra.Category.Grp.Zero
import all Mathlib.Algebra.Category.Ring.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import all Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.AlgebraicGeometry.Pullbacks
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all Mathlib.CategoryTheory.Adjunction.Triple
import all Mathlib.CategoryTheory.EffectiveEpi.Comp
import all Mathlib.CategoryTheory.Extensive
import all Mathlib.CategoryTheory.GradedObject.Bifunctor
import all Mathlib.CategoryTheory.GradedObject.Monoidal
import all Mathlib.CategoryTheory.GradedObject.Trifunctor
import all Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import all Mathlib.CategoryTheory.Limits.Preserves.Filtered
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import all Mathlib.CategoryTheory.Monad.Adjunction
import all Mathlib.CategoryTheory.Monoidal.Action.Basic
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.CommMon_
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Monoidal.Mod
import all Mathlib.CategoryTheory.Monoidal.Mon
import all Mathlib.CategoryTheory.MorphismProperty.Comma
import all Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import all Mathlib.CategoryTheory.Sites.Abelian
import all Mathlib.CategoryTheory.Sites.Coherent.Basic
import all Mathlib.CategoryTheory.Sites.Coherent.Comparison
import all Mathlib.CategoryTheory.Sites.ConcreteSheafification
import all Mathlib.CategoryTheory.Sites.Grothendieck
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.Combinatorics.Quiver.ReflQuiver
import all Mathlib.Data.Int.ConditionallyCompleteOrder
import all Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import all Mathlib.Geometry.RingedSpace.PresheafedSpace
import all Mathlib.Geometry.RingedSpace.SheafedSpace
import all Mathlib.Topology.Category.CompHausLike.Basic
import all Mathlib.Topology.Category.CompHausLike.Limits
import all Mathlib.Topology.Category.Profinite.Basic
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all Mathlib.Topology.Category.Profinite.Limits
import all Mathlib.Topology.Category.TopCat.Basic
import all Mathlib.Topology.Connected.TotallyDisconnected
import all Mathlib.Topology.ContinuousMap.Defs
import all WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import all WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import all WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
import all WeilConjectures.CategoryTheory.ModuleObjects.Free
import all Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import all WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import all WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import all WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
import all WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import all WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import all WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import all WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import all WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import all WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import all WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Continuity of derived Hom out of a stratum extension

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
sk-lem-constructible-ext-continuity-stratum.md and its proof
(blueprint: det-lem-constructible-ext-continuity-stratum).

The colimit is taken in complexes of coefficient modules, hence degreewise. Derived Hom
is taken in the ordinary unbounded derived category, using the same extension i_* u_! L
as the recorded stratum Hom lemma. The comparison is induced by the colimit cocone.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale

private theorem moduleColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (I : Type (u + 1)) [SmallCategory I] :
    HasColimitsOfShape I
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  infer_instance

attribute [local instance 2000] moduleColimits

private theorem complexColimits
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (I : Type (u + 1)) [SmallCategory I] :
    HasColimitsOfShape I (CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ) := by
  infer_instance

attribute [local instance 2000] complexColimits

set_option maxHeartbeats 800000 in
-- Derived module functors require additional elaboration heartbeats.
set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxSize 4096 in
private theorem qcqsFiniteFreeHomEvaluation
    (X : Scheme.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ X)).obj P))
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

set_option maxHeartbeats 800000 in
-- Derived module functors require additional elaboration heartbeats.
set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxSize 4096 in
private theorem freeComap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : Mod.IsFree S M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫
    (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular S) ≪≫
      biproduct.mapIso (fun _ ↦ ?_)⟩⟩
  simpa using Mod.regularIsoOfIsIso (inv φ)

set_option maxHeartbeats 800000 in
-- Derived module functors require additional elaboration heartbeats.
set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxSize 4096 in
private theorem lisseRawCover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (P : CondensedRing.supportModules Λ X) (hP : IsLisseCoefficientModule Λ P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj (condensedRingObj Λ X))
        (((upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ X)).obj P) := by
  obtain ⟨C, hC⟩ := hP
  refine ⟨C, fun s ↦ ?_⟩
  let α := condensedPullbackHom Λ (C.f s)
  let F := (upperStar Ab.{u + 1} (C.f s)).mapMod (condensedRingObj Λ X)
  let e := (Mod.extendScalarsIsoComapInv α).app (F.obj P)
  obtain ⟨n, ⟨b⟩⟩ := hC s
  have h' : Mod.IsFree _ ((Mod.comap (inv α)).obj (F.obj P)) :=
    ⟨n, ⟨e.symm ≪≫ b⟩⟩
  obtain ⟨m, ⟨c⟩⟩ := freeComap α h'
  let d := (Mod.comapComp α (inv α)).symm ≪≫
    Mod.comapCongr (show α ≫ inv α = 𝟙 _ by simp) ≪≫ Mod.comapId _
  exact ⟨m, ⟨(d.app _).symm ≪≫ c⟩⟩

end AlgebraicGeometry.ProEtale
