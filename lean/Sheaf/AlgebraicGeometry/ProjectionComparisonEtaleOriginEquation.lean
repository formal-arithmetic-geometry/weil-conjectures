/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# Etale-origin comparison of compact-support projection maps

Source: main-20261015 blueprint, sec-six-functors-basics/sk-prop-cohsm,
first paragraph of thm-pur-cohomological-smoothness.proof.md; Stacks Tags 0E48,
09AF and 0GL1 (blueprint: def-smooth-purity-projection-comparison-equation).

The auxiliary definitions expose the specified tensor and pullback identifications.
Both compact-support comparisons are the canonical proper/open comparisons at c.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the positive-level coefficient quotient, from the recorded coefficient
extension theorem. Source: Serre, Local Fields, II, section 2
(blueprint: def-smooth-purity-projection-comparison-equation). -/
instance projectionComparisonCoefficient_finite
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)] :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n (Fact.out : 1 ≤ n)

/-- The derived pullback comparison used in the target transport.
Source: Stacks Tag 099R
(blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonPullbackIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).leftDerivedFunctorIsoMapDerivedCategory.symm
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor ≪≫
    Functor.leftDerivedFunctorCompNatIso
      (Etale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f)
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    Functor.isoWhiskerLeft
      (Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).leftDerivedFunctorIsoMapDerivedCategory

/-- The canonical target transport from the comparison of pullback and tensor.
Source: Stacks Tags 07A4 and 099R (blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonTargetIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H)) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)) := by
  exact
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).mapIso
      (asIso ((projectionComparisonPullbackIso A f).hom.app H)) ≪≫
    ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) M).app
      ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H)).symm

/-- Tensor target used in the bounded-below witness.
Source: main-20261015 blueprint (blueprint: def-smooth-purity-projection-comparison-equation). -/
noncomputable def projectionComparisonTensor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :=
  (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H))

/-- The asserted equality, with every target identification written explicitly.
The left route is PF-pro, P of the specified target identification, then C at the tensor.
The right route is C at M tensor identity, the inverse comparison tensor map, then V(PF-et).
Source: Stacks Tag 0E48 and the blueprint projection comparison, displayed equation
(blueprint: def-smooth-purity-projection-comparison-equation). -/
@[irreducible] def ProjectionComparisonEquation (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor A (f := f) M H)) : Prop :=
  ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (projectionComparisonTargetIso A f M H).hom ≫
      (compactSupportSiteComparison A c).hom.app
        ⟨((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj H), hD⟩ =
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
      ((compactSupportSiteComparison A c).hom.app ⟨M, hM⟩)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj H) ≫
      ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} A)
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) c).obj M)).inv.app H) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app H)

/-- The full existential conclusion of the etale-origin comparison statement.
Source: main-20261015 blueprint, thm-pur-cohomological-smoothness.proof.md
(blueprint: def-smooth-purity-projection-comparison-equation). -/
@[irreducible] def projectionComparisonConclusion
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (H : Etale.DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hM : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) X M)
    (_hH : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) Y H)
    (_hTor : ∃ a b : ℤ, Etale.DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing l E n) Y a b H) : Prop :=
  ∃ (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hD : _root_.DerivedCategory.TStructure.t.plus
      (projectionComparisonTensor (Padic.coefficientExtensionRing l E n) (f := f) M H)),
    ProjectionComparisonEquation (Padic.coefficientExtensionRing l E n) c M H hM hD


end AlgebraicGeometry.ProEtale
