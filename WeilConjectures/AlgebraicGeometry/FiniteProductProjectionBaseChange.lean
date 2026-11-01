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
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.Open.OpenDirectImageFiniteCoefficients
import WeilConjectures.Compactification.Defs
import WeilConjectures.Compactification.Dense
import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
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

/-!
# Finite-coefficient base change along a product projection

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-tf-independent-base-change/_section.md, current order 3435
(the node retains historical main-20261023 order 2394)
(blueprint: sk-lem-tf-independent-base-change).

The exchange is the published ambient ringed mate with the canonical constant-ring
identifications. Bounded constructibility is expressed by the essential image of the
published finite-ring etale comparison, in the intrinsic constant-ring presentation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The chosen Cartesian square of the first projections and `f × id_T`.
Its pullback identification is the universal one supplied by the product square,
then preserved by the forgetful functor from schemes over the base.
Source: blueprint order 3435, the definitions of h, p_X and p_Y
(blueprint: sk-lem-tf-independent-base-change). -/
def finiteProductProjectionSquare (D : WeilConjectures.FiniteFieldDatum.{u})
    {X Y : Over (Spec (.of D.k))} (f : X ⟶ Y) (T : Over (Spec (.of D.k))) :
    ChosenCartesianSquare (prod.fst : X ⨯ T ⟶ X).left
      (prod.map f (𝟙 T)).left f.left (prod.fst : Y ⨯ T ⟶ Y).left :=
  { toCommSq := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget _)).toCommSq
    isoPullback := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget _)).isoPullback
    hom_fst := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget _)).isoPullback_hom_fst
    hom_snd := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget _)).isoPullback_hom_snd }

end AlgebraicGeometry.Scheme
