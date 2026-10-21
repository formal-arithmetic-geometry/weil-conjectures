/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyClass

import all Sheaf.AlgebraicGeometry.CommutativeExchangeClassCompatibility
import Sheaf.AlgebraicGeometry.CommutativeExchangeEvaluationCompatibility

import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility


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



attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

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


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem rawClass_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale)
    (z : (abelianHigherDirectImageRawPresheaf f q F).obj (op U)) :
    rawRestrictedCohomologyClass f q F U (rawRestrictedCohomologyComparison f q F U z) =
      z := by
  let := isIso_rawRestrictedCohomologyComparison f q F U
  apply (ConcreteCategory.bijective_of_isIso
    (rawRestrictedCohomologyComparison f q F U)).1
  exact rawRestrictedCohomologyClass_spec f q F U
    (rawRestrictedCohomologyComparison f q F U z)

private theorem class_restriction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (U V : Y.Etale) (i : V ⟶ U)
    (z : (abelianHigherDirectImageRawPresheaf f q F).obj (op U)) :
    abelianHigherDirectImageClass f q F V
        ((abelianHigherDirectImageRawPresheaf f q F).map i.op z) =
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.map i.op
        (abelianHigherDirectImageClass f q F U z) := by
  exact congrArg (fun k ↦ k z) ((comparisonPresheafMap f q F).naturality i.op)

private theorem adjunction_shifted_postcomp
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [R.CommShift ℤ] (adj : L ⊣ R)
    (n : ℤ) {A : C} {K K' : D} (z : L.obj A ⟶ K⟦n⟧) (a : K ⟶ K') :
    adj.homEquiv _ _ z ≫ (R.commShiftIso n).hom.app K ≫
        (shiftFunctor C n).map (R.map a) =
      adj.homEquiv _ _ (z ≫ (shiftFunctor D n).map a) ≫
        (R.commShiftIso n).hom.app K' := by
  rw [← Functor.commShiftIso_hom_naturality]
  rw [← Category.assoc, ← adj.homEquiv_naturality_right]

attribute [local irreducible] Functor.mapDerivedCategoryPlus Functor.rightDerivedFunctorPlus

-- Keep shift-comparison algebra abstract before specializing the derived functors.
private theorem adjunction_homology_postcomp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ]
    {L : C ⥤ D} {R : D ⥤ C} [R.CommShift ℤ] (adj : L ⊣ R)
    (H₀ Hq : C ⥤ E) (n : ℤ) (σ : shiftFunctor C n ⋙ H₀ ≅ Hq)
    {B : C} {A : E} (s : A ⟶ H₀.obj B)
    {T K K' : D} (c : L.obj B ⟶ T) (z : T ⟶ K⟦n⟧) (a : K ⟶ K') :
    (s ≫ H₀.map (adj.homEquiv _ _ (c ≫ z)) ≫
        (H₀.mapIso ((R.commShiftIso n).app K) ≪≫ σ.app (R.obj K)).hom) ≫
        Hq.map (R.map a) =
      s ≫ H₀.map (adj.homEquiv _ _ (c ≫ (z ≫ (shiftFunctor D n).map a))) ≫
        (H₀.mapIso ((R.commShiftIso n).app K') ≪≫ σ.app (R.obj K')).hom := by
  apply map_shifted_triangle_iso H₀ Hq n σ s _ _ _ _ _ _ rfl rfl
  simpa only [Iso.app_hom, Category.assoc] using
    adjunction_shifted_postcomp adj n (c ≫ z) a

private theorem class_coefficient {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G) (q : ℕ)
    (U : Y.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    abelianHigherDirectImageClass f q G U
        (z ≫ (shiftFunctor _ (q : ℤ)).map ((DerivedCategory.Plus.singleFunctor _ 0).map φ)) =
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((R+((f)_*[AddCommGrpCat.{u + 1}])).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map φ))).hom.app (op U)
        (abelianHigherDirectImageClass f q F U z) := by
  let H₀ := DerivedCategory.Plus.homologyFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let Hq := DerivedCategory.Plus.homologyFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
  let a := (DerivedCategory.Plus.singleFunctor _ 0).map φ
  let adj := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).derivedPlus
  let A := (abelianComparisonFree Y).obj U
  let c := (((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let K' := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  have hm := adjunction_homology_postcomp adj H₀ Hq (q : ℤ)
    (H₀.shiftIso (q : ℤ) 0 (q : ℤ) (add_zero _))
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A) c z a
  have hm' : higherClassMorphism f F q U z ≫
      Hq.map (R+((f)_*[AddCommGrpCat.{u + 1}]).map a) =
      higherClassMorphism f G q U (z ≫ (shiftFunctor _ (q : ℤ)).map a) := by
    dsimp only [higherClassMorphism, abelianComparisonShift, H₀, Hq, adj, A, c] at hm ⊢
    exact hm
  let T := Hq.map (R+((f)_*[AddCommGrpCat.{u + 1}]).map a)
  change _ = T.hom.app (op U) (abelianHigherDirectImageClass f q F U z)
  calc
    _ = freeRepresentableHomEquiv Y U _
        (higherClassMorphism f G q U (z ≫ (shiftFunctor _ (q : ℤ)).map a)) :=
      higher_class_evaluation f G q U _
    _ = freeRepresentableHomEquiv Y U _ (higherClassMorphism f F q U z ≫ T) :=
      congrArg (freeRepresentableHomEquiv Y U _) hm'.symm
    _ = T.hom.app (op U)
        (freeRepresentableHomEquiv Y U _ (higherClassMorphism f F q U z)) :=
      freeRepresentableHomEquiv_comp Y U _ T
    _ = _ := congrArg (T.hom.app (op U)) (higher_class_evaluation f F q U z).symm


private theorem adjunction_unit_natural_comp
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {A B : C} {T T' : D} (a : A ⟶ B) (E : L.obj A ⟶ T)
    (E' : L.obj B ⟶ T') (b : T ⟶ T') (he : L.map a ≫ E' = E ≫ b) :
    a ≫ adj.unit.app B ≫ R.map E' = adj.unit.app A ≫ R.map E ≫ R.map b := by
  rw [← Category.assoc, ← adj.unit_naturality]
  simp only [Category.assoc, ← R.map_comp]
  rw [he]

private theorem higherMap_coefficient
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : F ⟶ G) (q : ℕ) :
    ((g)^*[AddCommGrpCat.{u + 1}]).map
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((R+((f)_*[AddCommGrpCat.{u + 1}])).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map φ))) ≫
        exchangeChartHigherMap sq G q =
      exchangeChartHigherMap sq F q ≫
        (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
          ((R+((f')_*[AddCommGrpCat.{u + 1}])).map
            ((DerivedCategory.Plus.singleFunctor _ 0).map
              (((g')^*[AddCommGrpCat.{u + 1}]).map φ))) := by
  let S := DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let R := rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f
  let R' := rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f'
  let H' := DerivedCategory.Plus.homologyFunctor
    (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
  let α := Functor.whiskerLeft (S ⋙ R)
      ((((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso
        (q : ℤ)).hom) ≫
    Functor.whiskerLeft S
      (Functor.whiskerRight (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq) H') ≫
    Functor.whiskerRight
      ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom)
      (R' ⋙ H')
  have h := α.naturality φ
  simp only [α, S, R, R', H', exchangeChartHigherMap, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.comp_obj, Functor.map_comp, DerivedCategory.Plus.homologyFunctor,
    Category.assoc] at h ⊢
  exact h


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
  -- Use raw classes and derived evaluation instead of explicit resolution representatives.
  refine ⟨?_, ?_, ?_⟩
  · intro U x
    let z := rawRestrictedCohomologyClass f q F U x
    have hm : rawRestrictedCohomologyComparison f q F U ≫
        exchangeChartPullback sq F q U =
      commutativeExchangeRawPullbackMap sq F q U ≫
        rawRestrictedCohomologyComparison f' q _ (g.Etale.obj U) :=
      commutativeExchangeEvaluationCompatibility sq F q U
    have he := congrArg (fun m ↦ m z) hm
    simp only [ConcreteCategory.comp_apply] at he
    rw [rawRestrictedCohomologyClass_spec] at he
    have hr : rawRestrictedCohomologyClass f' q _ (g.Etale.obj U)
        (exchangeChartPullback sq F q U x) =
        commutativeExchangeRawPullbackMap sq F q U z := by
      let := isIso_rawRestrictedCohomologyComparison f' q
        (((g')^*[AddCommGrpCat.{u + 1}]).obj F) (g.Etale.obj U)
      apply (ConcreteCategory.bijective_of_isIso
        (rawRestrictedCohomologyComparison f' q _ (g.Etale.obj U))).1
      rw [rawRestrictedCohomologyClass_spec]
      exact he
    dsimp only [exchangeChartValue, exchangeChartTheta]
    rw [hr, commutativeExchangeRawPullbackMap_apply]
    exact commutativeExchangeClassCompatibility sq F q U z
  · intro G φ U x
    let a := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map φ))
    have he := higherMap_coefficient sq F G φ q
    have h : a ≫ (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app _ ≫
          ((g)_*[AddCommGrpCat.{u + 1}]).map (exchangeChartHigherMap sq G q) =
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app _ ≫
          ((g)_*[AddCommGrpCat.{u + 1}]).map (exchangeChartHigherMap sq F q) ≫
          ((g)_*[AddCommGrpCat.{u + 1}]).map
            ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
              ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f').map
                ((DerivedCategory.Plus.singleFunctor _ 0).map
                  (((g')^*[AddCommGrpCat.{u + 1}]).map φ)))) := by
      exact adjunction_unit_natural_comp
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g) a
        (exchangeChartHigherMap sq F q) (exchangeChartHigherMap sq G q) _ he
    dsimp only [exchangeChartValue, exchangeChartTheta]
    rw [rawClass_comparison, class_coefficient]
    exact congrArg (fun k ↦ k.hom.app (op U)
      (abelianHigherDirectImageClass f q F U (rawRestrictedCohomologyClass f q F U x))) h
  · intro U V i x
    let H := (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
    let t := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app H ≫
      ((g)_*[AddCommGrpCat.{u + 1}]).map (exchangeChartHigherMap sq F q)
    have hn := congrArg (fun k ↦ k (exchangeChartTheta f F q U x))
      (t.hom.naturality i.op)
    dsimp only [exchangeChartValue, exchangeChartTheta]
    rw [rawClass_comparison, class_restriction]
    exact hn

end AlgebraicGeometry.Etale
