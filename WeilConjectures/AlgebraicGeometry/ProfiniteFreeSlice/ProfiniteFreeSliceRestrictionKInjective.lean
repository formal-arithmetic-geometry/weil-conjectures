/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.WeaklyEtale
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # K-injective restriction for the actual internal coefficient pullback

Source: Stacks Project Tag 08FI, Lemma 21.20.1
(blueprint: new-c1-profinite-free-slice-restriction-kinjective).

Restriction has the exact weakly-etale extension-by-zero functor as a left
adjoint. The preservation theorem for right adjoints to exact functors therefore
applies directly to unbounded K-injective complexes of internal modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
open ModuleObjectRingedComparison

/-- Restriction along X[P] preserves unbounded K-injective complexes of internal modules.
Source: Stacks Project Tag 08FI, Lemma 21.20.1
(blueprint: new-c1-profinite-free-slice-restriction-kinjective).

Proof: the projection X[P] to X is weakly etale. The source library's
weaklyEtaleLowerShriekUpperStarAdjunction is an adjunction between the actual
internal module pullback and its extension-by-zero left adjoint. The latter is
additive and exact, with finite-limit and finite-colimit preservation already
proved in that source module. Apply Adjunction.preservesKInjectiveComplexes:
termwise adjunction sends a map from an acyclic complex into the restriction of
J to a map from its acyclic extension by zero into J. K-injectivity supplies a
null homotopy, and the additive adjunction transports that homotopy back.
This applies without boundedness or a monomorphism assumption, including empty
P and zero coefficients. No transport to section-module categories is needed. -/
theorem restrictionComplex_isKInjective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u})
    (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective] :
    CochainComplex.IsKInjective ((restrictionComplex Λ X P).obj J) := by
  let : WeaklyEtale (test X P).hom := (test X P).prop
  let : (restriction Λ X P).PreservesKInjectiveComplexes :=
    (CondensedRing.weaklyEtaleLowerShriekUpperStarAdjunction Λ
      (test X P).hom).preservesKInjectiveComplexes
  exact Functor.PreservesKInjectiveComplexes.isKInjective_map J

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
