/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Sheaf.AlgebraicGeometry.BoundedDerivedSmoothBaseChange
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.CondensedAmbientExchange

/-!
# Finite pro-etale smooth base change

Source: Weil conjectures blueprint, sec-smooth-base-change/sk-rem-rest, finite
pro-etale smooth-base-change paragraph; Stacks Project, Tags 0EYU and 0F09
(blueprint: sbc-thm-finite-proetale-smooth-base-change).

The input and output use the recorded continuous-function coefficient module category.
The ambient ringed mate is computed in fixed-scalar coordinates using the canonical
realization equivalence. This is the same unit--square--counit mate: realization
identifies the coefficient actions by constant scalar sections, transports the
adjunctions and their composition comparisons, and hence transports their mate.
No alternative exchange is chosen and no completion is taken.

## Main definitions

- `finiteSmoothModelCoordinates`: coordinates of an arbitrary etale model isomorphism.
- `finiteSmoothTargetComparison`: target comparison, deriving qcqs of the base change.

## Main statement

- `isIso_finite_proetale_smooth_base_change`: invertibility and the explicit
  conjugation identity for every etale model, in the ringed coefficient category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Express the specified ringed etale model isomorphism in fixed-scalar coordinates.
Source: blueprint finite pro-etale smooth-base-change paragraph
(blueprint: sbc-thm-finite-proetale-smooth-base-change).
The composition comparison identifies the dependency's derived site comparison
with site inverse image followed by realization. Its inverse, the given alpha,
and the realization unit fix the coordinates, including for identity alpha. -/
noncomputable def finiteSmoothModelCoordinates (T : Scheme.{u})
    (K : FiniteCoefficientDerivedCategory T Λ)
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (α : (finiteCoefficientDerivedComparison T Λ).obj (DerivedCategory.Plus.ι.obj L) ≅ K) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory.obj
        (DerivedCategory.Plus.ι.obj L) ≅
      (finiteCoefficientRealization T Λ).mapDerivedCategory.asEquivalence.inverse.obj K :=
  (finiteCoefficientRealization T Λ).mapDerivedCategory.asEquivalence.unitIso.app _ ≪≫
    (finiteCoefficientRealization T Λ).mapDerivedCategory.asEquivalence.inverse.mapIso
      (((Functor.mapDerivedCategoryCompIso
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
        (finiteCoefficientRealization T Λ)).symm.app (DerivedCategory.Plus.ι.obj L)) ≪≫ α)

/-- The canonical target comparison for the given square. Source: blueprint finite
pro-etale smooth-base-change paragraph; Stacks Tags 01K5 and 01KU
(blueprint: sbc-thm-finite-proetale-smooth-base-change).
The base-change permanence instances follow from the supplied cartesian square,
so qcqs of the second vertical edge is not an additional hypothesis. -/
noncomputable def finiteSmoothTargetComparison
    {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    [QuasiCompact g] [QuasiSeparated g] (sq : ChosenCartesianSquare h e p g) :
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).mapDerivedCategoryPlus ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctorPlus) ⋙
      DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory ≅
    DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor ⋙
          (lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctor := by
  have hp := (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
    sq.hom_fst sq.hom_snd).flip
  letI : QuasiCompact h := MorphismProperty.of_isPullback (P := @QuasiCompact) hp inferInstance
  letI : QuasiSeparated h :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) hp inferInstance
  exact baseChangeTargetComparisonIso e h Λ

/-- Finite pro-etale smooth base change, including its description for every etale model.
Source: blueprint, sec-smooth-base-change/sk-rem-rest, finite pro-etale paragraph;
Stacks Project, Tags 0EYU and 0F09
(blueprint: sbc-thm-finite-proetale-smooth-base-change).

Proof:
1. The recorded essential-image predicate gives a bounded constructible etale L and
an isomorphism alpha from its derived site inverse image to K. Boundedness implies
boundedness below, so regard L as an object of the bounded-below category.
2. Apply sbc-thm-bounded-derived-smooth-base-change, with the positive annihilator
and invertibility hypotheses collected in IsSmoothBaseChangeCoefficients. The exchange
is the canonical module mate of sbc-def-base-change-map, not a chosen endpoint map.
3. Base-change permanence makes h qcqs. The canonical comparison-direct-image and
comparison-pullback maps give baseChangeSourceComparisonIso and the target comparison.
Only L, not either exchange endpoint, needs to be bounded below.
4. The recorded lem-weil-pbc-transport-identifies-exchange identifies conjugation
of the etale exchange by these comparisons with derivedBaseChangeMap at nu-star L.
Every factor is invertible, giving invertibility there.
5. Naturality at finiteSmoothModelCoordinates alpha gives the displayed formula:
source of alpha inverse, source comparison inverse, site image of etale exchange,
target comparison, target of alpha. Applying the exact realization equivalence
writes both invertibility and that formula in the actual ringed coefficient category.
Realization preserves the specified scalar sections, adjunctions, and mates, so this
is the ordinary ambient ringed exchange. This works for every choice of L and alpha.
No boundedness or constructibility is imposed on the exchange endpoints. -/
theorem isIso_finite_proetale_smooth_base_change
    {S T Y X : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian S] [IsNoetherian T]
    [Smooth p] [QuasiCompact g] [QuasiSeparated g]
    (sq : ChosenCartesianSquare h e p g) (N : ℕ)
    (hcoeff : Etale.IsSmoothBaseChangeCoefficients N Λ S)
    (K : FiniteCoefficientDerivedCategory T Λ)
    (hK : isBoundedConstructibleFiniteCoefficient T Λ K) :
    IsIso ((finiteCoefficientRealization X Λ).mapDerivedCategory.map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app
        ((finiteCoefficientRealization T Λ).mapDerivedCategory.asEquivalence.inverse.obj K))) ∧
    ∀ (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (_hL : Etale.DerivedCategory.isBoundedConstructible Λ T (DerivedCategory.Plus.ι.obj L))
      (α : (finiteCoefficientDerivedComparison T Λ).obj (DerivedCategory.Plus.ι.obj L) ≅ K),
      (finiteCoefficientRealization X Λ).mapDerivedCategory.map
          ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app
            ((finiteCoefficientRealization T Λ).mapDerivedCategory.asEquivalence.inverse.obj K)) =
        (finiteCoefficientRealization X Λ).mapDerivedCategory.map
          (((lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor ⋙
              (upperStar (ModuleCat.{u + 1} Λ) p).leftDerivedFunctor).map
                (finiteSmoothModelCoordinates Λ T K L α).inv ≫
            (baseChangeSourceComparisonIso g p Λ).inv.app L ≫
            (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map
              (DerivedCategory.Plus.ι.map
                ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).app L)) ≫
            (finiteSmoothTargetComparison Λ sq).hom.app L ≫
            ((upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor ⋙
              (lowerStar (ModuleCat.{u + 1} Λ) h).rightDerivedFunctor).map
                (finiteSmoothModelCoordinates Λ T K L α).hom) := by
  sorry

end AlgebraicGeometry.ProEtale
