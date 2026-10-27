/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.CanonicalTateCompletedComparisons
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.Paper.PrincipalKoszulStrictReplacement
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange

/-! # Canonical Tate comparisons: ScalarComparisons

Source: current blueprint, def-pur-tate-datum, canonical root-line comparisons.
This module preserves the original unshifted comparison declarations.
(blueprint: def-pur-canonical-tate-scalar-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.CanonicalTate
open FrobeniusCoefficientTwists

attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived

attribute [-instance] PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] IntegralOnSlice.completion
  IntegralOnSlice.completionComparison IntegralOnSlice.completionUnit
  IntegralOnSlice.duality IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  HasDerivedCategory.standard completedIntegralCoefficientSheafUnrestricted
  coefficientTotalTensor SheafOfModules.monoidalCategory IntegralOnSlice.tower
  IntegralOnSlice.augmentation integralOperationsTensorTowerFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The finite module realization normalized on the actual adjunction unit.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons).
Proof: Both right adjoints are the same constant-coefficient direct image.
The unique isomorphism between their left adjoints is fixed by the unit square.
The displayed section formula is that square on each source section, and its
faithfulness proves uniqueness. It is the comparison used in finite tensor pullback. -/
theorem finiteRealization_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! e : finiteModulePull l E f n ≅ sfIntrinsicPullback
        (finiteCoefficientRing l E (n + 1)) f,
      ∀ (M : normalizedDVRModules l E Y n) (V : Y.ProEt)
        (x : M.val.obj (op V)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange f).obj V))
          (finiteModuleSection l E f n M V x) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op V) x := by
  exact openSquarePullbackModel_existsUnique (finiteCoefficientRing l E (n + 1)) f

/-- The uniquely unit-normalized ordinary finite realization.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def finiteRealization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (finiteRealization_existsUnique l E f n).exists.choose

/-- The finite twist pullback comparison computed by the exact module inverse image.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def finitePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (n r : ℕ) :
    (finiteDerivedPullback l E n f).obj
        (DerivedCategory.Q.obj (finiteComplex l E Y n r)) ≅
      DerivedCategory.Q.obj (finiteComplex l E X n r) := by
  letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  exact ((Functor.mapDerivedCategoryNatIso (finiteRealization l E f n)).app
      (DerivedCategory.Q.obj (finiteComplex l E Y n r))).symm ≪≫
    ((finiteModulePull l E f n).mapDerivedCategorySingleFunctor 0).app
      (finiteCoefficientTwist l E Y n (r : ℤ)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (finitePullSheaf l E f n r)

/-- The rational pullback comparison is the image of the specified integral one.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def rationalPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (r : ℕ) :
    (rationalDerivedPullback l E f).obj (sfRationalTwistingCoefficient l E Y (r : ℤ)) ≅
      sfRationalTwistingCoefficient l E X (r : ℤ) :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1
      (sfRationalTwistingCoefficient l E Y (r : ℤ))) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (integralPull l E f r))

/-- The rational tensor-power identification is the localized integral identification.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def rationalProduct (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r s : ℕ) :
    (rationalDerivedTensor l E X).obj
        (sfRationalTwistingCoefficient l E X (r : ℤ),
          sfRationalTwistingCoefficient l E X (s : ℤ)) ≅
      sfRationalTwistingCoefficient l E X ((r + s : ℕ) : ℤ) :=
  eqToIso ((rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1
      (sfRationalTwistingCoefficient l E X (r : ℤ),
        sfRationalTwistingCoefficient l E X (s : ℤ))) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (integralProduct l E X r s))

/-- The finite Frobenius arrow transported to the intrinsic pullback used by tensor.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def finiteTau {X : Scheme.{u}} (g : X ⟶ X) [IsIso g] (n r : ℕ) :
    (finiteDerivedPullback l E n g).obj
        (DerivedCategory.Q.obj (finiteComplex l E X n r)) ≅
      DerivedCategory.Q.obj (finiteComplex l E X n r) := by
  letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) g
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) g
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) g
  exact ((Functor.mapDerivedCategoryNatIso (finiteRealization l E g n)).app
      (DerivedCategory.Q.obj (finiteComplex l E X n r))).symm ≪≫
    finiteDerivedLineMap l E g n (r : ℤ)

/-- The integral Frobenius arrow in the full constructible subcategory.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def integralTau {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)] (r : ℕ) :
    (constructibleIntegralPullback l E g).obj
        (sfIntegralTwistingCoefficient l E X (r : ℤ)) ≅
      sfIntegralTwistingCoefficient l E X (r : ℤ) :=
  ObjectProperty.isoMk _ (integralDerivedLineMap l E g (r : ℤ))

/-- Canonical commutation of finite pullbacks around an actual commuting scheme square.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def finiteSquare {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    (h : g' ≫ w = w ≫ g) (n : ℕ) :
    finiteDerivedPullback l E n g ⋙ finiteDerivedPullback l E n w ≅
      finiteDerivedPullback l E n w ⋙ finiteDerivedPullback l E n g' :=
  (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) w g).symm ≪≫
    eqToIso (congrArg (finiteDerivedPullback l E n) h.symm) ≪≫
    sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) g' w

/-- Canonical commutation of completed pullbacks, using the prescribed composition maps.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def integralSquare {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] (h : g' ≫ w = w ≫ g) :
    constructibleIntegralPullback l E g ⋙ constructibleIntegralPullback l E w ≅
      constructibleIntegralPullback l E w ⋙ constructibleIntegralPullback l E g' :=
  (pullbackTensorIntegralComposition l E g w).symm ≪≫
    eqToIso (congrArg (fun k : X ⟶ Y ↦
      @constructibleIntegralPullback l _ E _ _ _ X Y k hX hY) h.symm) ≪≫
    pullbackTensorIntegralComposition l E w g'

/-- Canonical commutation of rational pullbacks on the unchanged integral objects.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def rationalSquare {X Y : Scheme.{u}} (w : X ⟶ Y) (g : Y ⟶ Y) (g' : X ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (h : g' ≫ w = w ≫ g)
    (M : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E w).obj ((rationalDerivedPullback l E g).obj M) ≅
      (rationalDerivedPullback l E g').obj ((rationalDerivedPullback l E w).obj M) :=
  (pullbackTensorRationalComposition l E g w M).symm ≪≫
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj M) h.symm) ≪≫
    pullbackTensorRationalComposition l E w g' M

/-- The completed scalar comparison on a line, fixed by ordinary scalar extension.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons).
Proof: The scalar-completion map is invertible on the complete line. Its
inverse identifies completed extension with the published ordinary derived
scalar functor. The single-functor comparison and twistLineScalarIso finish
the computation; their unit tensor formulas fix every map and its inverse uniquely. -/
theorem integralScalarLine_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r : ℕ) :
    ∃! e : (integralScalarExtension l E L ι X).obj
        (sfIntegralTwistingObject l E X (r : ℤ)) ≅
      sfIntegralTwistingObject l L X (r : ℤ),
      (scalarCompletion l E L ι X).app (sfIntegralTwistingObject l E X (r : ℤ)) ≫
        e.hom =
      ((integralOrdinaryScalar l E L ι X).mapDerivedCategorySingleFunctor 0).hom.app
        (integralTwistLine l E X (r : ℤ)) ≫
      (DerivedCategory.singleFunctor _ 0).map (twistLineScalarIso l E X L ι (r : ℤ)).hom := by
  let e := (scalarCompletionIso l E L ι X
      (sfIntegralTwistingObject l E X (r : ℤ))
      (sfIntegralTwistingObject_mem l E X (r : ℤ)).1).symm ≪≫
    ((integralOrdinaryScalar l E L ι X).mapDerivedCategorySingleFunctor 0).app
      (integralTwistLine l E X (r : ℤ)) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (twistLineScalarIso l E X L ι (r : ℤ))
  refine ⟨e, ?_, ?_⟩
  · simp [e, scalarCompletionIso]
  · intro e' he'
    apply Iso.ext
    have : IsIso ((scalarCompletion l E L ι X).app
        (sfIntegralTwistingObject l E X (r : ℤ))) :=
      (scalarCompletion_existsUnique l E L ι X).exists.choose_spec.2 _
        (sfIntegralTwistingObject_mem l E X (r : ℤ)).1
    apply (cancel_epi ((scalarCompletion l E L ι X).app
      (sfIntegralTwistingObject l E X (r : ℤ)))).1
    simpa [e, scalarCompletionIso] using he'

/-- The specified completed scalar extension of a Tate line.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def integralScalarLine
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r : ℕ) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι X).obj (sfIntegralTwistingCoefficient l E X (r : ℤ)) ≅
      sfIntegralTwistingCoefficient l L X (r : ℤ) :=
  ObjectProperty.isoMk _ (integralScalarLine_existsUnique l E L ι X r).exists.choose

/-- The rational coefficient-line comparison is the localized completed scalar map.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def rationalScalarLine
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (r : ℕ) :
    (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
        (sfRationalTwistingCoefficient l E X (r : ℤ)) ≅
      sfRationalTwistingCoefficient l L X (r : ℤ) :=
  eqToIso ((sfRationalScalarExtension_existsUnique l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec.2.1
        (sfRationalTwistingCoefficient l E X (r : ℤ))) ≪≫
    (sfRationalConstructibleLocalization l L X).mapIso (integralScalarLine l E L ι X r)

/-- The quotient balancing is fixed on every compatible pure root tensor.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons).
Proof: Scalar extension carries the unit image of each pure root tensor
to that same ordered root tensor. Linearity and sheafification determine a unique
map. Locally both lines are the quotient coefficient unit, hence the map is an
isomorphism. This also includes identity reduction and exponent zero. -/
theorem finiteScalarSheaf_existsUnique (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] {m n : ℕ} (h : n ≤ m) (r : ℕ) :
    ∃! e : (coefficientFiniteQuotientExtension l E X h).obj
        (finiteCoefficientTwist l E X m (r : ℤ)) ≅
      finiteCoefficientTwist l E X n (r : ℤ),
      ∀ (U : X.ProEtᵒᵖ) (x : Fin r → (purTwistZlOne X l).obj.obj U),
        e.hom.val.app U (coefficientFiniteQuotientUnitSection l E X h
          (finiteCoefficientTwist l E X m (r : ℤ)) U
          (finiteTateProPowerGenerator l E m X U 1 r x)) =
        finiteTateProPowerGenerator l E n X U 1 r x := by
  sorry

/-- The canonical finite quotient comparison computed on its flat single complex.
Source: blueprint def-pur-tate-datum, canonical roots and tensor powers
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def finiteScalarLine (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] {m n : ℕ} (h : n ≤ m) (r : ℕ) :
    (coefficientFiniteQuotientDerived l E X h).obj
        (DerivedCategory.Q.obj (finiteComplex l E X m r)) ≅
      DerivedCategory.Q.obj (finiteComplex l E X n r) :=
  coefficientFiniteQuotientModel l E X h (finiteComplex l E X m r)
      (finiteGood l E X m r) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (coefficientFiniteQuotientExtension l E X h) (.up ℤ) 0).app
          (finiteCoefficientTwist l E X m (r : ℤ))) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (finiteScalarSheaf_existsUnique l E X h r).exists.choose

/-- The integral reduction counit is invertible on the actual flat root complex.
Source: Stacks 06YY; blueprint root quotient systems
(blueprint: def-pur-canonical-tate-scalar-comparisons).
Proof: the degree-zero line is flat and its single complex is K-flat. The defining
universal scalar-extension counit is invertible on every K-flat complex. -/
theorem integralReductionCounit_isIso (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (n r : ℕ) :
    IsIso ((scalarReductionCounit l E X n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (integralComplex l E X r))) := by
  exact (scalarReductionDerivedExistence l E X n).choose_spec.choose_spec.2.2
    (integralComplex l E X r) (integralGood l E X r).1

/-- Integral reduction computed by its specified homotopy counit and root tensor map.
Source: blueprint canonical finite quotients of Tate lines
(blueprint: def-pur-canonical-tate-scalar-comparisons). -/
def integralReductionLine (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] (n r : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj
        (sfIntegralTwistingObject l E X (r : ℤ)) ≅
      DerivedCategory.Q.obj (finiteComplex l E X n r) := by
  letI := integralReductionCounit_isIso l E X n r
  exact (scalarReductionDerivedExtension l E X n).mapIso
      ((DerivedCategory.quotientCompQhIso _).app (integralComplex l E X r)).symm ≪≫
    asIso ((scalarReductionCounit l E X n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (integralComplex l E X r))) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (scalarReductionExtension l E X n) (.up ℤ) 0).app
          (integralTwistLine l E X (r : ℤ))) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((((signedTwistReduction_comparison l E X).1 n).exists.choose_spec.2
        (r : ℤ)).exists.choose)

end WeilConjectures.CanonicalTate
