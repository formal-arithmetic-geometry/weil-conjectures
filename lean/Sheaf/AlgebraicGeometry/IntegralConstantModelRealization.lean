/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W6
-/
module

public import Sheaf.Paper.IntegralCriterionReductions
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
public import Sheaf.Paper.AdicStratifiedPerfectData
import all Sheaf.Paper.IntegralCriterionReductions

/-! # Canonical integral constant-model realization

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), and the
projection-normalized integral coefficient comparison.
(blueprint: def-sfb-integral-constant-model-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint

namespace AlgebraicGeometry.ProEtale.IntegralConstantModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The spectral and absolute-value coefficient presentations have the same ring object.
Source: the projection-normalized integral coefficient comparison
(blueprint: def-sfb-integral-constant-model-realization). -/
theorem pointEquality :
    Mon.mk (DerivedNakayama.integerRing l E) = sfbCondensedIntegers l E :=
  integralPointMon_eq l E

/-- The identity comparison of the two equal point coefficient presentations.
Source: the spectral-norm integral coefficient comparison
(blueprint: def-sfb-integral-constant-model-realization). -/
def pointComparison : Mon.mk (DerivedNakayama.integerRing l E) ≅ sfbCondensedIntegers l E :=
  eqToIso (pointEquality l E)

/-- The actual section-and-coefficient functor; its action changes only scalar actions.
Source: the normalized coefficient projections of the integral criterion
(blueprint: def-sfb-integral-constant-model-realization). -/
def modulesFunctor (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (sfbCondensedIntegers l E).X X) ⥤
      Scheme.proEtaleRingModules X
        (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal) :=
  Mod.comap (coefficientMap (pointComparison l E).hom.hom X) ⋙
    integralSectionFunctor l E X ⋙
    SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom ⋙
    Scheme.pbcRestrict (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom

/-- The composite functor acts by the four displayed ordinary scalar transports.
Source: the normalized integral coefficient comparison
(blueprint: def-sfb-integral-constant-model-realization). -/
theorem modulesFunctor_obj (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (sfbCondensedIntegers l E).X X)) :
    (modulesFunctor l E X).obj M =
      (Scheme.pbcRestrict
        (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom).obj
        ((SheafOfModules.restrictScalars
          (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
          ((integralSectionFunctor l E X).obj
            ((Mod.comap (coefficientMap (pointComparison l E).hom.hom X)).obj M))) := rfl

/-- Each coefficient map used by the functor is an isomorphism.
Source: the finite-projection integral coefficient comparisons
(blueprint: def-sfb-integral-constant-model-realization). -/
instance modulesFunctor_isEquivalence (X : Scheme.{u}) :
    (modulesFunctor l E X).IsEquivalence := by
  have : (Mod.comap (coefficientMap (pointComparison l E).hom.hom X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (coefficientMap (pointComparison l E).hom.hom X)).isEquivalence_functor
  have : (Scheme.pbcRestrict
      (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom).IsEquivalence :=
    restriction_isEquivalence ((Scheme.adicLisseForget X).mapIso
      (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)))
  have : (integralSectionFunctor l E X).IsEquivalence :=
    (integralSectionFunctor_properties l E X).2
  have : (SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom).IsEquivalence :=
    restriction_isEquivalence (Scheme.integralDetailedCoefficientComparison X l E)
  unfold modulesFunctor
  exact Functor.isEquivalence_trans _ _


/-- The ordinary realization preserves addition, since all its factors preserve products.
Source: Stacks Tag 00YV
(blueprint: def-sfb-integral-constant-model-realization). -/
instance modulesFunctor_additive (X : Scheme.{u}) : (modulesFunctor l E X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Termwise localization of the canonical ordinary realization.
Source: Stacks Tags 00YV and 05RU
(blueprint: def-sfb-integral-constant-model-realization). -/
def derived (X : Scheme.{u}) := (modulesFunctor l E X).mapDerivedCategory.asEquivalence

end AlgebraicGeometry.ProEtale.IntegralConstantModel
