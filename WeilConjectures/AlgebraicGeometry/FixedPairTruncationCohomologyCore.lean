/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfWeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.SfCommonStageWeilCohomology
public import WeilConjectures.AlgebraicGeometry.ConstructibleTruncations
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackCompletedComparison
public import WeilConjectures.SixFunctors.FrobeniusPointTransportNatural
public import WeilConjectures.AlgebraicGeometry.CoefficientCohomologyModules
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
import WeilConjectures.AlgebraicGeometry.AutomorphismConstructibleStageEquivalence
import WeilConjectures.AlgebraicGeometry.FieldWeilShriekShiftData
import WeilConjectures.AlgebraicGeometry.IsomorphismFieldTransport
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import all Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Specifications for truncations of rational Weil pairs

Source: current blueprint sec-poincare-duality/sk-thm-frobenius,
prop-weil-operations.proof.md, sentence 2 and the final cohomology assertion;
BBD, Proposition 1.3.3 and paragraph 1.3.4, printed pp. 29--30
(blueprint: def-pod-fixed-pair-truncation-specifications).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v uC vC
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence HasDerivedCategory.standard
  Scheme.residueField
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Aut

/-- The clauses of the fixed-pair assertion, using the existing transport functor.
The boundary equation includes the specified shift comparison. Triangles are taken
only in C. Source: blueprint prop-weil-operations, truncation and cohomology clauses
(blueprint: def-pod-fixed-pair-truncation-specifications). -/
def FixedPairTruncationCohomologySpec
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (t : TStructure C) (P : C ⥤ C) [P.CommShift ℤ] : Prop :=
  ∃ (cLE : ∀ m : ℤ, t.truncLE m ⋙ P ≅ P ⋙ t.truncLE m)
    (cGE : ∀ m : ℤ, t.truncGE m ⋙ P ≅ P ⋙ t.truncGE m),
    (∀ (m : ℤ) (K : C),
      (cLE m).hom.app K ≫ (t.truncLEι m).app (P.obj K) =
        P.map ((t.truncLEι m).app K) ∧
      P.map ((t.truncGEπ m).app K) ≫ (cGE m).hom.app K =
        (t.truncGEπ m).app (P.obj K)) ∧
    (∀ m : ℤ,
      IsoAlgebra.mapOfNatIso (cLE m) ⋙ IsoAlgebra.forget P =
        IsoAlgebra.forget P ⋙ t.truncLE m ∧
      IsoAlgebra.mapOfNatIso (cGE m) ⋙ IsoAlgebra.forget P =
        IsoAlgebra.forget P ⋙ t.truncGE m) ∧
    (∀ (m : ℤ) (K : IsoAlgebra P),
      ((IsoAlgebra.mapOfNatIso (cLE m)).obj K).str.hom ≫
          (t.truncLEι m).app K.carrier =
        P.map ((t.truncLEι m).app K.carrier) ≫ K.str.hom ∧
      K.str.hom ≫ (t.truncGEπ m).app K.carrier =
        P.map ((t.truncGEπ m).app K.carrier) ≫
          ((IsoAlgebra.mapOfNatIso (cGE m)).obj K).str.hom ∧
      ((IsoAlgebra.mapOfNatIso (cGE (m + 1))).obj K).str.hom ≫
          (t.truncGEδLE m (m + 1) rfl).app K.carrier =
        P.map ((t.truncGEδLE m (m + 1) rfl).app K.carrier) ≫
          (P.commShiftIso (1 : ℤ)).hom.app ((t.truncLE m).obj K.carrier) ≫
            (shiftFunctor C (1 : ℤ)).map
              (((IsoAlgebra.mapOfNatIso (cLE m)).obj K).str.hom)) ∧
    (∀ i : ℤ,
      ∃ H : IsoAlgebra P ⥤ IsoAlgebra P,
        H = (IsoAlgebra.mapOfNatIso (cLE i) ⋙ IsoAlgebra.mapOfNatIso (cGE i)) ⋙
          IsoAlgebra.mapOfNatIso (P.commShiftIso i) ∧
        H ⋙ IsoAlgebra.forget P =
          IsoAlgebra.forget P ⋙ constructibleTruncationCohomology t i ∧
        ∀ K : IsoAlgebra P, t.heart (H.obj K).carrier)



variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
/-- The rational shift is the localization of the signed Roos shift, through the
recorded full-subcategory inclusion. Its integral witness retains both the coordinate
normalization and descent equations; an arbitrary shift is not accepted.
Source: blueprint prop-weil-operations, exact Frobenius pullback; Stacks 014E, 0941
(blueprint: def-pod-fixed-pair-truncation-specifications). -/
def FixedPairRationalShiftNormalization
    (s : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ) : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  ∃ c : IntegralCompletedComparison.Comparison l E (D.geometricFrobenius Y₀).hom,
    ∃ d : (constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).CommShift ℤ,
      (fun [_ambientShift : (integralDerivedPullback l E
          (D.geometricFrobenius Y₀).hom).CommShift ℤ]
        [_integralShift : (constructibleIntegralPullback l E
          (D.geometricFrobenius Y₀).hom).CommShift ℤ]
        [_rationalShift : (sfWeilFrobeniusPullback D l hl Y₀ E).CommShift ℤ] ↦
        (∀ (K : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left) (r : ℤ),
          (sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι.map
              (((constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).commShiftIso
                 r).hom.app K) ≫
            (((sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι).commShiftIso
               r).hom.app
                ((constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).obj K) =
          (integralDerivedPullback l E (D.geometricFrobenius Y₀).hom).map
              ((((sfIntegralConstructible l E (D.geometricFiber Y₀).left).ι).commShiftIso
                 r).hom.app K) ≫
            ((integralDerivedPullback l E (D.geometricFrobenius Y₀).hom).commShiftIso
               r).hom.app K.obj) ∧
        ∃ β : sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left ⋙
              sfWeilFrobeniusPullback D l hl Y₀ E ≅
            constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom ⋙
              sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left,
          (∀ K, β.hom.app K = eqToHom
            ((rationalDerivedPullback_existsUnique l E
              (D.geometricFrobenius Y₀).hom).exists.choose_spec.2.1
              ((sfRationalConstructibleLocalization l E (D.geometricFiber Y₀).left).obj K))) ∧
          NatTrans.CommShift β.hom ℤ)
        (_ambientShift := c.derivedShift) (_integralShift := d) (_rationalShift := s)


attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι

/-- The standard rational t-structure on the actual geometric fibre.
Source: blueprint prop-constructible-truncations
(blueprint: def-pod-fixed-pair-truncation-specifications). -/
def fixedPairRationalTStructure :=
  sfRationalStandardTStructure l E (D.geometricFiber Y₀).left D hl

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The corresponding standard common-stage t-structure.
Source: blueprint prop-constructible-truncations
(blueprint: def-pod-fixed-pair-truncation-specifications). -/
def fixedPairCommonStageTStructure :=
  sfCommonStageStandardTStructure l (D.geometricFiber Y₀).left Ω D hl

/-- Compatibility with every finite stage specifies the common-stage shift.
The component of the inclusion comparison is the actual object identification of
commonStageDerivedPullback, so it is not an unspecified commuting isomorphism.
Source: blueprint common-stage coefficient convention and exact Frobenius pullback
(blueprint: def-pod-fixed-pair-truncation-specifications). -/
def FixedPairCommonShiftNormalization
    (s : ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
      (sfWeilFrobeniusPullback D l hl Y₀
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).CommShift ℤ)
    (q : (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).CommShift ℤ) : Prop :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl Y₀ x
  ∀ L : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ β : sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) ⋙
          GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L ≅
        GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L ⋙
          sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω,
      (∀ K, β.inv.app K = eqToHom
        ((commonStageDerivedPullback_existsUnique l Ω
          (D.geometricFrobenius Y₀).hom).exists.choose_spec.1
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).obj K))) ∧
      ∀ (r : ℤ) (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω
          (D.geometricFiber Y₀).left L),
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).map
            ((Functor.commShiftIso (sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)) (self := s L) r).hom.app K) ≫
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).commShiftIso r).hom.app
            ((sfWeilFrobeniusPullback D l hl Y₀
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).obj K) ≫
          (shiftFunctor _ r).map (β.hom.app K) =
        β.hom.app ((shiftFunctor _ r).obj K) ≫
          (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω).map
            (((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).commShiftIso r).hom.app K) ≫
          (Functor.commShiftIso (sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω)
            (self := q) r).hom.app
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := Ω) (Y := (D.geometricFiber Y₀).left) L).obj K)


end WeilConjectures
