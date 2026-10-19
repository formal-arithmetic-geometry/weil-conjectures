/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyClass

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Limits.MorphismProperty
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf

/-!
# Commutative-square exchange on etale cohomology charts

Source: Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7;
etale-cohomology.tex, Tags 03Q8 and 0EYM
(blueprint: lem-kun-commutative-exchange-chart).

The chart cohomology uses the existing `rawAffineRestrictedCohomology`, whose
chosen chart is `U ×_Y X`. This differs from `X ×_Y U` only by the canonical
symmetry. Its raw derived-Hom presentation and inverse evaluation map are the
existing constructions. No representative, section map, or comparison is
chosen from an existence statement.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

/-- The canonical map from chart cohomology to the evaluated higher direct image:
inverse evaluation, derived adjunction, homology and the represented generator.
Source: Stacks Project, Tag 03Q8
(blueprint: lem-kun-commutative-exchange-chart). -/
noncomputable def exchangeChartTheta {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale)
    (x : rawAffineRestrictedCohomology f q F U) :
    ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.obj (op U) :=
  abelianHigherDirectImageClass f q F U (rawRestrictedCohomologyClass f q F U x)

/-- The degree-q exchange sheaf morphism, including exact inverse-image homology
and the inverse-image single-complex identification at its endpoints.
Source: Stacks Project, Tags 0736 and 07A7
(blueprint: lem-kun-commutative-exchange-chart). -/
noncomputable def exchangeChartHigherMap
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((g)^*[AddCommGrpCat.{u + 1}]).obj
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ⟶
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((g')^*[AddCommGrpCat.{u + 1}]).obj F))) :=
  (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
    (q : ℤ)).hom.app _ ≫
  (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      (rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
        ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F))

/-- The left side of the chart identity: theta, the sheaf inverse-image unit on
sections over U, then the degree-q derived exchange evaluated on `g.Etale.obj U`.
Source: Stacks Project, Tags 0736, 03Q8 and 0EYM
(blueprint: lem-kun-commutative-exchange-chart). -/
noncomputable def exchangeChartValue
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale)
    (x : rawAffineRestrictedCohomology f q F U) :
    ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((g')^*[AddCommGrpCat.{u + 1}]).obj F)))).obj.obj (op (g.Etale.obj U)) :=
  (exchangeChartHigherMap sq F q).hom.app (op (g.Etale.obj U))
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app _).hom.app
      (op U) (exchangeChartTheta f F q U x))

/-- The induced map `U' ×_Y' X' → U ×_Y X`, where `U' = U ×_Y Y'`.
Both components are induced by the original commutative square.
Source: Stacks Project, Tags 0736 and 0EYM
(blueprint: lem-kun-commutative-exchange-chart). -/
noncomputable def exchangeChartMorphism
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g) (U : Y.Etale) :
    pullback (g.Etale.obj U).hom f' ⟶ pullback U.hom f :=
  pullback.map (g.Etale.obj U).hom f' U.hom f
    (pullback.fst U.hom g) g' g (pullback.condition (f := U.hom) (g := g)).symm sq.w.symm

/-- The coefficient composition identification for the induced chart map.
The equality in the second composition comparison is its second projection formula.
Source: Stacks Project, Tags 03CB, 0736 and 0EYM
(blueprint: lem-kun-commutative-exchange-chart). -/
noncomputable def exchangeChartCoefficientMap
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : Y.Etale) :
    ((exchangeChartMorphism sq U)^*[AddCommGrpCat.{u + 1}]).obj
      (((pullback.snd U.hom f)^*[AddCommGrpCat.{u + 1}]).obj F) ⟶
    ((pullback.snd (g.Etale.obj U).hom f')^*[AddCommGrpCat.{u + 1}]).obj
      (((g')^*[AddCommGrpCat.{u + 1}]).obj F) :=
  (upperStarComp AddCommGrpCat.{u + 1} (exchangeChartMorphism sq U)
    (pullback.snd U.hom f)).inv.app F ≫
  (upperStarComp AddCommGrpCat.{u + 1} (pullback.snd (g.Etale.obj U).hom f') g'
    (exchangeChartMorphism sq U ≫ pullback.snd U.hom f)
    (pullback.lift_snd _ _ _)).hom.app F

/-- Canonical cohomology pullback along the actual chart map, followed by the
coefficient composition identification. This uses the existing derived-sections
pullback on a complex, not an arbitrary raw-class map or sheafification isomorphism.
Source: Stacks Project, Tags 0736, 03Q8 and 0EYM
(blueprint: lem-kun-commutative-exchange-chart). -/
noncomputable def exchangeChartPullback
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale) :
    rawAffineRestrictedCohomology f q F U ⟶
    rawAffineRestrictedCohomology f' q
      (((g')^*[AddCommGrpCat.{u + 1}]).obj F) (g.Etale.obj U) :=
  rawAffineComplexPullback (q : ℤ) (exchangeChartMorphism sq U)
    ((CochainComplex.singleFunctor _ 0).obj
      (((pullback.snd U.hom f)^*[AddCommGrpCat.{u + 1}]).obj F)) ≫
  (cohomology AddCommGrpCat.{u + 1} (pullback (g.Etale.obj U).hom f') (q : ℤ)).map
    (DerivedCategory.Q.map
      ((((exchangeChartMorphism sq U)^*[AddCommGrpCat.{u + 1}]).mapCochainComplexSingleFunctor
        0).hom.app _ ≫
        (CochainComplex.singleFunctor _ 0).map (exchangeChartCoefficientMap sq F U)))

/-- Commutative-square derived exchange agrees with cohomology pullback on every
etale chart. The second and third clauses state naturality in the coefficient
sheaf and in a morphism of test objects, using postcomposition and restriction
of the existing raw-cohomology presheaf to express the input maps.

Source: Stacks Project, Tags 0736 and 07A7; Tag 03Q8 and the chart diagram of 0EYM
(blueprint: lem-kun-commutative-exchange-chart).

Proof:
1. Choose bounded-below injective representatives I of F[0] and J of g'^*F[0],
   and a quasi-isomorphism g'^*I → J. Exact inverse image preserves the
   resolution; no injectivity of g'^*I is asserted (enough-injectives,
   dplus-injective-representative, kinjective-hom-derived, inverse-image-exact).
2. Write the representative of exchange as the f'-unit followed by f'_* of
   the square comparison, the g'^* f-counit, and I → J. Counit naturality and
   the triangle identity show its transpose is the defining derived mate
   (commutative-derived-exchange, derived-inverse-image-adjunction,
   derived-inverse-image-composition).
3. For a sheaf B, the horizontal transpose of underived exchange is f_* of
   the g'-unit followed by the direct-image square comparison. Substitute
   the two composition-unit formulas, move the f-counit through the g'-unit
   by naturality, and cancel the f triangle. Evaluation at U is exactly the
   section pullback along U' ×_Y' X' → U ×_Y X, followed by I → J
   (inverse-image-composition and etale-inverse-image-restriction).
4. The chart projections are etale. Restriction preserves injectives and
   quasi-isomorphisms, so I and J restricted to these charts compute their
   cohomology. The preceding section chain map therefore computes t^*
   (etale-base-change-finite-limits, etale-restriction-injectives,
   cohomology-pullback).
5. A class in H^q(I(U ×_Y X)) is represented by a section cycle. The canonical
   presheaf-to-sheaf map sends it to its sheaf cohomology class. The inverse
   image unit and exact-functor homology comparison preserve cycle inclusions
   and boundary quotients. Applying H^q of the exchange representative gives
   the same class as the section pullback computed in step 3, proving the
   first equation (higher-direct-image-presheaf, exact-functor-complex-cohomology).
6. For restriction in U, sheaf maps, units and the fibre-product arrows
   commute with restriction. For a coefficient morphism F → G, choose maps
   between injective representatives using the K-injective Hom bijection.
   The two composites after g'^* agree in the derived category, hence are
   homotopic because their target is K-injective. Restrict and evaluate this
   homotopy. Taking cycles modulo boundaries gives the two naturality clauses
   (kinjective-hom-derived, cohomology-pullback-functorial). The same argument
   with the identity coefficient map proves independence of resolutions.
-/
theorem commutativeExchangeChart
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (∀ (U : Y.Etale) (x : rawAffineRestrictedCohomology f q F U),
      exchangeChartValue sq F q U x =
        exchangeChartTheta f' _ q (g.Etale.obj U) (exchangeChartPullback sq F q U x)) ∧
    (∀ (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G)
      (U : Y.Etale) (x : rawAffineRestrictedCohomology f q F U),
      exchangeChartValue sq G q U
        (rawRestrictedCohomologyComparison f q G U
          (rawRestrictedCohomologyClass f q F U x ≫
            (shiftFunctor _ (q : ℤ)).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ))) =
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (((g')^*[AddCommGrpCat.{u + 1}]).map φ)))).hom.app (op (g.Etale.obj U))
        (exchangeChartValue sq F q U x)) ∧
    (∀ (U V : Y.Etale) (i : V ⟶ U) (x : rawAffineRestrictedCohomology f q F U),
      exchangeChartValue sq F q V
        (rawRestrictedCohomologyComparison f q F V
          ((abelianHigherDirectImageRawPresheaf f q F).map i.op
            (rawRestrictedCohomologyClass f q F U x))) =
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (((g')^*[AddCommGrpCat.{u + 1}]).obj F)))).obj.map (g.Etale.map i).op
        (exchangeChartValue sq F q U x)) := by
  sorry

end AlgebraicGeometry.Etale
