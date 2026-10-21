/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianFreeRepresentablePullback
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
public import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Raw classes over a commutative square

The source is transported by inverse-image composition and the canonical
pullback isomorphism for a free represented sheaf. No cohomology comparison is
inverted in this construction. Point evaluation is cached by its explicit
degree-zero and shift formula.
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

section ExactTransport

variable {C C' : Type*} [Category* C] [Category* C'] [Abelian C] [Abelian C']
  [HasDerivedCategory C] [HasDerivedCategory C']
  (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (q : ℕ) {G F : C} {G' : C'} (e : P.obj G ≅ G')

/-- Exact inverse image on a shifted derived-Hom class, with its source identified
by an isomorphism. Every factor is a canonical single or shift comparison.
Source: Stacks Project, Tag 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
noncomputable def commutativeExchangeTransport
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj G' ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.obj F))⟦(q : ℤ)⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map e.inv ≫
    (P.mapDerivedCategoryPlusSingleFunctor 0).inv.app G ≫
    P.mapDerivedCategoryPlus.map z ≫
    (P.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (q : ℤ)).map
      ((P.mapDerivedCategoryPlusSingleFunctor 0).hom.app F)

/-- The explicit single and shift formula for the exact transport.
Source: Stacks Project, Tag 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
theorem commutativeExchangeTransport_def
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    commutativeExchangeTransport P q e z =
      (DerivedCategory.Plus.singleFunctor _ 0).map e.inv ≫
        (P.mapDerivedCategoryPlusSingleFunctor 0).inv.app G ≫
        P.mapDerivedCategoryPlus.map z ≫
        (P.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
        (shiftFunctor _ (q : ℤ)).map
          ((P.mapDerivedCategoryPlusSingleFunctor 0).hom.app F) := by
  rfl

/-- Exact transport preserves the zero class, by additivity of every functor.
Source: Stacks Project, Tag 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
theorem commutativeExchangeTransport_zero :
    commutativeExchangeTransport P q e (F := F) 0 = 0 := by
  simp [commutativeExchangeTransport]

/-- Exact transport preserves sums, by additivity and bilinearity of composition.
Source: Stacks Project, Tag 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
theorem commutativeExchangeTransport_add
    (z z' : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    commutativeExchangeTransport P q e (z + z') =
      commutativeExchangeTransport P q e z + commutativeExchangeTransport P q e z' := by
  simp [commutativeExchangeTransport, Preadditive.comp_add, Preadditive.add_comp]

end ExactTransport

attribute [irreducible] commutativeExchangeTransport

section ExactTransportHom

variable {C C' : Type*} [Category* C] [Category* C'] [Abelian C] [Abelian C']
  [HasDerivedCategory.{u + 1} C] [HasDerivedCategory.{u + 1} C']
  (P : C ⥤ C') [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  (q : ℕ) {G F : C} {G' : C'} (e : P.obj G ≅ G')

/-- Bundle exact transport as an additive map on derived-Hom groups.
Source: Stacks Project, Tag 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
noncomputable def commutativeExchangeTransportHom :
    AddCommGrpCat.of ((DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) ⟶
    AddCommGrpCat.of ((DerivedCategory.Plus.singleFunctor _ 0).obj G' ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.obj F))⟦(q : ℤ)⟧) :=
  AddCommGrpCat.ofHom
    { toFun := commutativeExchangeTransport P q e
      map_zero' := commutativeExchangeTransport_zero P q e
      map_add' := commutativeExchangeTransport_add P q e }

/-- The bundled map evaluates to the specified exact transport.
Source: Stacks Project, Tag 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
theorem commutativeExchangeTransportHom_apply
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    commutativeExchangeTransportHom P q e z = commutativeExchangeTransport P q e z := by
  rfl

end ExactTransportHom

attribute [irreducible] commutativeExchangeTransportHom

section ExactEvaluation

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{u + 1} C] [HasDerivedCategory D] [EnoughInjectives D]
  [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (R : D ⥤ AddCommGrpCat.{u + 1}) [R.Additive] [PreservesFiniteLimits R]
  (q : ℕ) (G F : C)

/-- The additive map evaluating shifted derived-Hom classes at a fixed section.
Source: Stacks Project, Tags 03Q8 and 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
noncomputable def commutativeExchangeEvaluationHom (γ : R.obj (L.obj G)) :
    AddCommGrpCat.of ((DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) ⟶
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      (R.rightDerivedFunctor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor _ 0).obj (L.obj F)))) :=
  RawRestrictedComparison.Evaluation.evaluate
      (RawRestrictedComparison.Evaluation.functor L R ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0)
      ((RawRestrictedComparison.Evaluation.zeroIso L R G).inv γ) ≫
    (RawRestrictedComparison.Evaluation.shiftIso L R q F).hom

/-- Evaluate a shifted derived-Hom class after exact restriction and derived sections.
All factors are the specified degree-zero and shift comparisons.
Source: Stacks Project, Tags 03Q8 and 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
noncomputable def commutativeExchangeEvaluation
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)
    (γ : R.obj (L.obj G)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      (R.rightDerivedFunctor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor _ 0).obj (L.obj F)))) :=
  commutativeExchangeEvaluationHom L R q G F γ z

/-- Point evaluation of the additive evaluation map.
Source: Stacks Project, Tags 03Q8 and 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
theorem commutativeExchangeEvaluationHom_apply
    (γ : R.obj (L.obj G))
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    commutativeExchangeEvaluationHom L R q G F γ z =
      commutativeExchangeEvaluation L R q G F z γ := by
  rfl

/-- The explicit formula for cached evaluation.
Source: Stacks Project, Tags 03Q8 and 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback).

Proof: Both expressions are the same composite evaluation construction. -/
theorem commutativeExchangeEvaluation_def
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj G ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧)
    (γ : R.obj (L.obj G)) :
    commutativeExchangeEvaluation L R q G F z γ =
      (RawRestrictedComparison.Evaluation.shiftIso L R q F).hom
        ((RawRestrictedComparison.Evaluation.functor L R ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map z
          ((RawRestrictedComparison.Evaluation.zeroIso L R G).inv γ)) := by
  rfl

end ExactEvaluation

attribute [irreducible] commutativeExchangeEvaluation commutativeExchangeEvaluationHom

/-- The native raw comparison is bundled evaluation at the represented generator.
This equation caches the definitional change of presentation of its derived-Hom group.
Source: Stacks Project, Tags 03Q8, 072W and 0BKV.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
theorem commutativeExchangeEvaluationHom_rawComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale) :
    let V := pullback U.hom f
    let L := upperStar AddCommGrpCat.{u + 1} (Z := V) (Y := X) (pullback.snd U.hom f)
    let R := Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}
    rawRestrictedCohomologyComparison f q F U =
      commutativeExchangeEvaluationHom L R q
          (((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U)) F
          (RawRestrictedComparison.generator f U) := by
  unfold commutativeExchangeEvaluationHom
  rfl

/-- The source comparison for pulling back a represented raw class.
Source: Stacks Project, Tags 03CB and 03Q8.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
noncomputable def commutativeExchangeRawSourceIso
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g) (U : Y.Etale) :
    ((g')^*[AddCommGrpCat.{u + 1}]).obj
      (((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U)) ≅
    ((f')^*[AddCommGrpCat.{u + 1}]).obj
      ((abelianComparisonFree Y').obj (g.Etale.obj U)) :=
  ((squareUpperStarIso AddCommGrpCat.{u + 1} sq).symm.app _) ≪≫
    ((f')^*[AddCommGrpCat.{u + 1}]).mapIso (abelianFreeRepresentablePullbackIso g U)

/-- Pullback of a raw derived-Hom class, with its represented source transported
by the actual square and the canonical free-sheaf pullback isomorphism.
Source: Stacks Project, Tags 03Q8 and 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
noncomputable def commutativeExchangeRawPullback
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((f')^*[AddCommGrpCat.{u + 1}]).obj
        ((abelianComparisonFree Y').obj (g.Etale.obj U))) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((g')^*[AddCommGrpCat.{u + 1}]).obj F))⟦(q : ℤ)⟧ :=
  commutativeExchangeTransport ((g')^*[AddCommGrpCat.{u + 1}]) q
    (commutativeExchangeRawSourceIso sq U) z

set_option backward.isDefEq.respectTransparency false in
/-- Raw transport as an actual homomorphism of raw higher-image groups.
Its underlying function is the explicit derived-Hom construction above.
Source: Stacks Project, Tags 03Q8 and 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
noncomputable def commutativeExchangeRawPullbackMap
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale) :
    (abelianHigherDirectImageRawPresheaf f q F).obj (op U) ⟶
    (abelianHigherDirectImageRawPresheaf f' q
      (((g')^*[AddCommGrpCat.{u + 1}]).obj F)).obj (op (g.Etale.obj U)) := by
  exact commutativeExchangeTransportHom ((g')^*[AddCommGrpCat.{u + 1}]) q
    (commutativeExchangeRawSourceIso sq U)

/-- The bundled raw map is the explicit exact-inverse-image transport with
identity target coefficient. Source: Stacks Project, Tag 07A6.
(blueprint: def-kun-commutative-exchange-raw-pullback). -/
theorem commutativeExchangeRawPullbackMap_apply
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (U : Y.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((f)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree Y).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) :
    commutativeExchangeRawPullbackMap sq F q U z =
      commutativeExchangeRawPullback sq F q U z := by
  unfold commutativeExchangeRawPullbackMap
  exact commutativeExchangeTransportHom_apply _ _ _ z

end AlgebraicGeometry.Etale
