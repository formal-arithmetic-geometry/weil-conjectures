/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.AlgebraicGeometry.Open.OpenDirectImageFiniteCoefficients
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.AlgebraicGeometry.OpenDirectImageFieldBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Coefficient.ProEtaleCoefficientModulePullbackComposition
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Product-projection exchange through a compactification

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-tf-independent-base-change/det-tf-ibc-pasting.md, order 3437;
Stacks Project, Tag 0E46 (blueprint: det-tf-ibc-pasting).

The helpers specialize the published ambient exchange and construct its canonical
right-adjoint composition maps. The supplied factorization is written as `j ≫ p`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The direct-image compositor, conjugate to the canonical constant-ring pullback
compositor under the specified derived adjunctions. This fixes the usual K-injective
composition identification, including its unit and counit normalization.
Source: blueprint order 3437, endpoint identifications; Stacks Tags 0D6E and 0E46
(blueprint: det-tf-ibc-pasting). -/
def compactificationDirectImageComposition (A : Type u) [CommRing A]
    {X B Y : Scheme.{u}} (j : X ⟶ B) (p : B ⟶ Y) :
    (proEtaleConstantRingPushforward A (j ≫ p)).rightDerivedFunctor ≅
      (proEtaleConstantRingPushforward A j).rightDerivedFunctor ⋙
        (proEtaleConstantRingPushforward A p).rightDerivedFunctor :=
  conjugateIsoEquiv
    (proEtaleRingDerivedAdjunction (j ≫ p) (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison (j ≫ p) A))
    ((proEtaleRingDerivedAdjunction p (proEtaleConstantRing Y A)
      (proEtaleConstantRing B A) (proEtaleConstantRingComparison p A)).comp
      (proEtaleRingDerivedAdjunction j (proEtaleConstantRing B A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison j A)))
    (proEtaleConstantRingPullbackComposition j p A)

/-- The same canonical compositor after taking the product with `T`, transported by
`prod.map_comp_id` so its source uses exactly `(p ∘ j) × id_T`.
Source: blueprint order 3437, last endpoint identification; Stacks Tag 0E46
(blueprint: det-tf-ibc-pasting). -/
def compactificationProductDirectImageComposition (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X B Y : Over S} (j : X ⟶ B) (p : B ⟶ Y) (T : Over S) :
    (proEtaleConstantRingPushforward A (prod.map (j ≫ p) (𝟙 T)).left).rightDerivedFunctor ≅
      (proEtaleConstantRingPushforward A (prod.map j (𝟙 T)).left).rightDerivedFunctor ⋙
        (proEtaleConstantRingPushforward A (prod.map p (𝟙 T)).left).rightDerivedFunctor :=
  eqToIso (congrArg
    (fun q : X ⨯ T ⟶ Y ⨯ T ↦ (proEtaleConstantRingPushforward A q.left).rightDerivedFunctor)
    (prod.map_comp_id j p)) ≪≫
      compactificationDirectImageComposition A (prod.map j (𝟙 T)).left
        (prod.map p (𝟙 T)).left

end AlgebraicGeometry.Scheme
