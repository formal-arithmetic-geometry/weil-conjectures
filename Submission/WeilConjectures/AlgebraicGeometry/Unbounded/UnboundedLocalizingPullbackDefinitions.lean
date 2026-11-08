/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Submission.WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Submission.WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Submission.WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Submission.WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The canonical localizing pullback preservation proposition

Source: blueprint latest, sec-six-functors-basics/sk-prop-proper-base-change-unbounded,
sk-prop-proper-base-change-unbounded-pullback.proof.md, exactness, sums and localizing closures
(blueprint: def-zl-unbounded-localizing-pullback).

These two declarations are moved from
`WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback` with their
names, signatures, and bodies unchanged. The canonical shift is constructed from the
existing exact-derived comparison; the proposition records the ambient and restricted
preservation clauses without asserting them. The localizing hull and constant-model
constructibility are the existing imported definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical shift-commutation of the total derived inverse image `Lg^*`: the one of the
termwise functor `D(g^*)` (Mathlib's `Functor.mapDerivedCategory`), transported along the
canonical isomorphism `CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`. Exactness of
`Lg^*` is asserted for this shift structure, not for an arbitrary one.
Source: blueprint main-20261015, inverse image on the localizing categories
(blueprint: def-zl-unbounded-localizing-pullback). -/
@[instance_reducible]
def unboundedLocalizingPullbackCommShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) :
    (CondensedRing.upperStar Λ g).leftDerivedFunctor.CommShift ℤ :=
  Functor.CommShift.ofIso (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm ℤ

attribute [local instance] unboundedLocalizingPullbackCommShift

set_option maxHeartbeats 800000 in
-- Elaborating inherited full-subcategory shift structures needs a larger heartbeat budget.
/-- The clauses of inverse-image preservation, including its restriction along the full
inclusions. `Lg^*` carries its canonical shift-commutation
`unboundedLocalizingPullbackCommShift`; the restriction is Mathlib's `ObjectProperty.lift` of
`Lg^*` along the full inclusions, with its inherited shift-commutation, and the triangulations
on the restricted categories are the inherited ones.
Source: blueprint main-20261015, inverse image on the localizing categories
(blueprint: def-zl-unbounded-localizing-pullback). -/
structure UnboundedLocalizingPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) : Prop where
  exact : (CondensedRing.upperStar Λ g).leftDerivedFunctor.IsTriangulated
  sums : ∀ I : Type (u + 2),
    PreservesColimitsOfShape (Discrete I) (CondensedRing.upperStar Λ g).leftDerivedFunctor
  constructible : ∀ K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
    (constantModelBoundedConstructible Λ Y K ∧ DerivedCategory.finiteTorAmplitude _ K) →
    constantModelBoundedConstructible Λ Y'
        ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K) ∧
      DerivedCategory.finiteTorAmplitude _
        ((CondensedRing.upperStar Λ g).leftDerivedFunctor.obj K)
  localizing : ∀ K : (localizingClosureProEtale Λ Y).FullSubcategory,
    localizingClosureProEtale Λ Y'
      (((localizingClosureProEtale Λ Y).ι ⋙ (CondensedRing.upperStar Λ g).leftDerivedFunctor).obj K)
  [sourceTriangulated : (localizingClosureProEtale Λ Y).IsTriangulated]
  [targetTriangulated : (localizingClosureProEtale Λ Y').IsTriangulated]
  restrictionExact : ((localizingClosureProEtale Λ Y').lift
    ((localizingClosureProEtale Λ Y).ι ⋙ (CondensedRing.upperStar Λ g).leftDerivedFunctor)
    localizing).IsTriangulated
  restrictionSums : ∀ I : Type (u + 2), PreservesColimitsOfShape (Discrete I)
    ((localizingClosureProEtale Λ Y').lift
      ((localizingClosureProEtale Λ Y).ι ⋙ (CondensedRing.upperStar Λ g).leftDerivedFunctor)
      localizing)

end AlgebraicGeometry.ProEtale
