/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.TraceFormula.TwoTermDeterminantPullbackCoherence
public import Sheaf.TraceFormula.TwoTermPerfectTorWindow

/-! # Affine and cartesian determinant-functor interfaces

The affine interface isolates the ring calculation from gluing over a general scheme.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
variable [d : ∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [∀ (X : Scheme.{u}) (U : X.Opens),
    HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]

/-- Determinant functors and their cartesian comparisons, relative to fixed coherent
pullback comparisons. Source: Stacks Project, Tags 0FJX and 0FJY
(blueprint: lem-trf-two-term-determinant-affine-descent). -/
structure TwoTermDeterminantFunctorData
    (κ : TwoTermDeterminantPullbackCoherence.{u, w}) where
  /-- The determinant functor for each scheme. -/
  functor : ∀ X : Scheme.{u}, TwoTermPerfectCore X ⥤ Core X.Modules
  /-- Each value is invertible, using the recorded scheme notion. -/
  invertible : ∀ (X : Scheme.{u}) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L), (twoTermDeterminantValue (functor X) L hL).IsInvertible
  /-- The canonical comparison to the displayed exterior-power formula. -/
  modelIso : ∀ {X : Scheme.{u}} (P : TwoTermDeterminantModel X),
    twoTermDeterminantValue (functor X) (DerivedCategory.Q.obj P.complex) (twoTermPerfect_model P) ≅
      P.line
  /-- The determinant of the zero complex is the structure sheaf. -/
  zeroIso : ∀ X : Scheme.{u},
    twoTermDeterminantValue (functor X) (twoTermDeterminantZeroObject X) (twoTermPerfect_zero X) ≅
      SheafOfModules.unit X.ringCatSheaf
  /-- For the contractible model the comparison to zero is evaluation, in dual-first order. -/
  acyclic : ∀ (X : Scheme.{u}) (E : X.Modules) (n : ℕ)
    (hE : E.IsFiniteLocallyFreeOfRank n),
    ∃ z : DerivedCategory.Q.obj (TwoTermDeterminantModel.identity E n hE).complex ≅
      twoTermDeterminantZeroObject X,
      (modelIso (TwoTermDeterminantModel.identity E n hE)).inv ≫
        (twoTermDeterminantIso (functor X)
          (twoTermPerfect_model (TwoTermDeterminantModel.identity E n hE))
          (twoTermPerfect_zero X) z).hom ≫
        (zeroIso X).hom =
      (β_ (dual (exteriorSheaf E n)) (exteriorSheaf E n)).hom ≫
        dualEvaluation (exteriorSheaf E n)
  /-- The natural determinant pullback comparison. -/
  pullbackIso : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L),
    (tensorPullback g).obj (twoTermDeterminantValue (functor X) L hL) ≅
      twoTermDeterminantValue (functor Y) ((derivedPullback g).obj L)
        (twoTermPerfect_pullback g L hL)
  /-- Naturality for every derived isomorphism. -/
  pullback_naturality : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X)
    {L M : schemeDerivedCategory X} (hL : isTwoTermPerfect X L)
    (hM : isTwoTermPerfect X M) (e : L ≅ M),
    (tensorPullback g).map (twoTermDeterminantIso (functor X) hL hM e).hom ≫
        (pullbackIso g M hM).hom =
      (pullbackIso g L hL).hom ≫
        (twoTermDeterminantIso (functor Y) (twoTermPerfect_pullback g L hL)
          (twoTermPerfect_pullback g M hM)
          ((derivedPullback g).mapIso e)).hom
  /-- Compatibility with identity pullback. -/
  pullback_id : ∀ (X : Scheme.{u}) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L),
    (pullbackIso (𝟙 X) L hL).hom ≫
        (twoTermDeterminantIso (functor X) (twoTermPerfect_pullback (𝟙 X) L hL) hL
          ((κ.derivedId X).app L)).hom =
      (twoTermDeterminantPullbackId X).hom.app (twoTermDeterminantValue (functor X) L hL)
  /-- Compatibility with composition, including successive restrictions to opens. -/
  pullback_comp : ∀ {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y)
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L),
    (tensorPullbackSectionComp h g).hom.app
        (twoTermDeterminantValue (functor X) L hL) ≫
        (tensorPullback h).map (pullbackIso g L hL).hom ≫
        (pullbackIso h ((derivedPullback g).obj L) (twoTermPerfect_pullback g L hL)).hom ≫
        (twoTermDeterminantIso (functor Z)
          (twoTermPerfect_pullback h ((derivedPullback g).obj L) (twoTermPerfect_pullback g L hL))
          (twoTermPerfect_pullback (h ≫ g) L hL)
          ((κ.derivedComp h g).app L)).hom =
      (pullbackIso (h ≫ g) L hL).hom


/-- The affine determinant construction, including arbitrary maps of affine schemes.
The hypothesis applies to the schemes, not to the ranks of the model terms.
Source: Stacks Project, More on Algebra, Tag 0FJM, and Perfect Complexes, Tag 0FJY
(blueprint: lem-trf-affine-two-term-determinant). -/
structure AffineTwoTermDeterminantData
    (κ : TwoTermDeterminantPullbackCoherence.{u, w}) where
  /-- The determinant functor for each scheme. -/
  functor : ∀ (X : Scheme.{u}) [IsAffine X], TwoTermPerfectCore X ⥤ Core X.Modules
  /-- Each value is invertible, using the recorded scheme notion. -/
  invertible : ∀ (X : Scheme.{u}) [IsAffine X] (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L), (twoTermDeterminantValue (functor X) L hL).IsInvertible
  /-- The natural determinant pullback comparison. -/
  pullbackIso : ∀ {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (g : Y ⟶ X) (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L),
    (tensorPullback g).obj (twoTermDeterminantValue (functor X) L hL) ≅
      twoTermDeterminantValue (functor Y) ((derivedPullback g).obj L)
        (twoTermPerfect_pullback g L hL)
  /-- Naturality for every derived isomorphism. -/
  pullback_naturality : ∀ {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    {L M : schemeDerivedCategory X} (hL : isTwoTermPerfect X L)
    (hM : isTwoTermPerfect X M) (e : L ≅ M),
    (tensorPullback g).map (twoTermDeterminantIso (functor X) hL hM e).hom ≫
        (pullbackIso g M hM).hom =
      (pullbackIso g L hL).hom ≫
        (twoTermDeterminantIso (functor Y) (twoTermPerfect_pullback g L hL)
          (twoTermPerfect_pullback g M hM)
          ((derivedPullback g).mapIso e)).hom
  /-- Compatibility with identity pullback. -/
  pullback_id : ∀ (X : Scheme.{u}) [IsAffine X] (L : schemeDerivedCategory X)
    (hL : isTwoTermPerfect X L),
    (pullbackIso (𝟙 X) L hL).hom ≫
        (twoTermDeterminantIso (functor X) (twoTermPerfect_pullback (𝟙 X) L hL) hL
          ((κ.derivedId X).app L)).hom =
      (twoTermDeterminantPullbackId X).hom.app (twoTermDeterminantValue (functor X) L hL)
  /-- Compatibility with composition, including successive restrictions to opens. -/
  pullback_comp : ∀ {X Y Z : Scheme.{u}}
    [IsAffine X] [IsAffine Y] [IsAffine Z] (g : Y ⟶ X) (h : Z ⟶ Y)
    (L : schemeDerivedCategory X) (hL : isTwoTermPerfect X L),
    (tensorPullbackSectionComp h g).hom.app
        (twoTermDeterminantValue (functor X) L hL) ≫
        (tensorPullback h).map (pullbackIso g L hL).hom ≫
        (pullbackIso h ((derivedPullback g).obj L) (twoTermPerfect_pullback g L hL)).hom ≫
        (twoTermDeterminantIso (functor Z)
          (twoTermPerfect_pullback h ((derivedPullback g).obj L) (twoTermPerfect_pullback g L hL))
          (twoTermPerfect_pullback (h ≫ g) L hL)
          ((κ.derivedComp h g).app L)).hom =
      (pullbackIso (h ≫ g) L hL).hom

  /-- The exterior formula over any model scheme, evaluated on affine test schemes. -/
  local_modelIso : ∀ {X Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ X) (P : TwoTermDeterminantModel X),
    (tensorPullback f).obj P.line ≅
      twoTermDeterminantValue (functor Y)
        ((derivedPullback f).obj (DerivedCategory.Q.obj P.complex)) (twoTermPerfect_pullback
          f _ (twoTermPerfect_model P))
  /-- The local exterior formula commutes with further affine base change. -/
  local_model_naturality : ∀ {X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (h : Z ⟶ Y) (P : TwoTermDeterminantModel X),
    (tensorPullbackSectionComp h f).hom.app P.line ≫
        (tensorPullback h).map (local_modelIso f P).hom ≫
        (pullbackIso h ((derivedPullback f).obj (DerivedCategory.Q.obj P.complex))
          (twoTermPerfect_pullback f _ (twoTermPerfect_model P))).hom ≫
        (twoTermDeterminantIso (functor Z)
          (twoTermPerfect_pullback h _ (twoTermPerfect_pullback f _ (twoTermPerfect_model
            P))) (twoTermPerfect_pullback (h ≫ f) _ (twoTermPerfect_model P))
          ((κ.derivedComp h f).app (DerivedCategory.Q.obj P.complex))).hom =
      (local_modelIso (h ≫ f) P).hom
  /-- The local determinant of zero has its unit trivialization. -/
  local_zeroIso : ∀ {X Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ X),
    (tensorPullback f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      twoTermDeterminantValue (functor Y)
        ((derivedPullback f).obj (twoTermDeterminantZeroObject X)) (twoTermPerfect_pullback f
          _ (twoTermPerfect_zero X))
  /-- The local zero trivialization commutes with further affine base change. -/
  local_zero_naturality : ∀ {X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (h : Z ⟶ Y),
    (tensorPullbackSectionComp h f).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (tensorPullback h).map (local_zeroIso f).hom ≫
        (pullbackIso h ((derivedPullback f).obj (twoTermDeterminantZeroObject X))
          (twoTermPerfect_pullback f _ (twoTermPerfect_zero X))).hom ≫
        (twoTermDeterminantIso (functor Z)
          (twoTermPerfect_pullback h _ (twoTermPerfect_pullback f _ (twoTermPerfect_zero X)))
            (twoTermPerfect_pullback (h ≫ f) _ (twoTermPerfect_zero X))
          ((κ.derivedComp h f).app (twoTermDeterminantZeroObject X))).hom =
      (local_zeroIso (h ≫ f)).hom
  /-- Evaluation in a global contractible model is respected on every affine test scheme. -/
  local_acyclic : ∀ (X : Scheme.{u}) (E : X.Modules) (n : ℕ)
    (hE : E.IsFiniteLocallyFreeOfRank n),
    ∃ z : DerivedCategory.Q.obj (TwoTermDeterminantModel.identity E n hE).complex ≅
      twoTermDeterminantZeroObject X,
      ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X),
        (local_modelIso f (TwoTermDeterminantModel.identity E n hE)).hom ≫
            (twoTermDeterminantIso (functor Y)
              (twoTermPerfect_pullback f _
                (twoTermPerfect_model (TwoTermDeterminantModel.identity E n hE)))
              (twoTermPerfect_pullback f _ (twoTermPerfect_zero X)) ((derivedPullback
                f).mapIso z)).hom =
          (tensorPullback f).map
              ((β_ (dual (exteriorSheaf E n)) (exteriorSheaf E n)).hom ≫
                dualEvaluation (exteriorSheaf E n)) ≫
            (local_zeroIso f).hom

end AlgebraicGeometry
