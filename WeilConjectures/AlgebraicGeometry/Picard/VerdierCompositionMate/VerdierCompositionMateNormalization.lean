/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.VerdierPairing.VerdierPairingThreeTransposes
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.Algebra.Field.Shrink
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SmoothPurity.Support.SupportScalarProjectionNormalization
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalSupportProjectionIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation

/-! # Composition mate and normalization of Verdier exchange

Source: literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-thm-frobenius/prop-weil-operations.proof.md, formal duality exchange;
sec-six-functors/sk-thm-sf-package/fix-cor-verdier-exchange.proof.md, Steps 1--2,
and fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-pod-verdier-composition-mate-normalization).

The formulas use the recorded fixed-pair domains and adjunctions. There is no
exceptional adjoint on an ambient category. The internal-adjunction isomorphism
is supplied only in the final, conditional normalization assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z vx vy vz vb
open CategoryTheory CategoryTheory.Endofunctor Opposite AlgebraicGeometry
open WeilConjectures.VerdierPairing

namespace WeilConjectures.VerdierCompositionMate

section Mate
variable {X : Type v} {Y : Type w} {S : Type z}
  [Category.{vx} X] [Category.{vy} Y] [Category.{vz} S]
  {ΦX : X ⥤ X} {ΦY : Y ⥤ Y} {ΦS : S ⥤ S}
  {F : X ⥤ Y} {G : Y ⥤ X} {H : Y ⥤ S} {J : S ⥤ Y}
  {U : X ⥤ S} {W : S ⥤ X}

end Mate

section Transposition
variable {X : Type v} {Y : Type w} [Category.{vx} X] [Category.{vy} Y]
  {ΦX : X ⥤ X} {ΦY : Y ⥤ Y}
  {F : X ⥤ Y} {G : Y ⥤ X} {P : Y ⥤ X} {Q : X ⥤ Y}

/-- The exceptional transpose of inverse projection followed by counit evaluation.
Source: fix-lem-tensor-adjunction.proof.md, Step 1
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def exceptionalTranspose
    (e : LiftedAdjunction ΦX ΦY F G) (_o : LiftedAdjunction ΦY ΦX P Q)
    (x : TensorHomData ΦX) (y : TensorHomData ΦY) (omega : Y) (M : X)
    (ay : y.tensor.obj (F.obj M) ⊣ y.hom.obj (op (F.obj M)))
    (pi : (y.tensor.obj (F.obj M)).obj ((y.hom.obj (op (F.obj M))).obj omega) ≅
      F.obj ((x.tensor.obj M).obj
        (P.obj ((y.hom.obj (op (F.obj M))).obj omega)))) :
    (x.tensor.obj M).obj (P.obj ((y.hom.obj (op (F.obj M))).obj omega)) ⟶
      G.obj omega :=
  e.adj.homEquiv _ _ (pi.inv ≫ ay.counit.app omega)

/-- Apply the last two transposes in tensor--Hom then ordinary-adjunction order.
Source: fix-cor-verdier-exchange.proof.md, Step 2
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def lastTransposes (o : LiftedAdjunction ΦY ΦX P Q) (x : TensorHomData ΦX)
    (M : X) (ax : x.tensor.obj M ⊣ x.hom.obj (op M)) {A : Y} {N : X}
    (t : (x.tensor.obj M).obj (P.obj A) ⟶ N) :
    A ⟶ Q.obj ((x.hom.obj (op M)).obj N) :=
  o.adj.homEquiv _ _ (ax.homEquiv _ _ t)

end Transposition

end WeilConjectures.VerdierCompositionMate

namespace WeilConjectures.VerdierCompositionMate

section Components
variable {X : Type v} {Y : Type w} [Category.{vx} X] [Category.{vy} Y]
  {ΦX : X ⥤ X} {ΦY : Y ⥤ Y}
  {F : X ⥤ Y} {G : Y ⥤ X} {P : Y ⥤ X} {Q : X ⥤ Y}

/-- The exchange component substitutes c before the final tensor--Hom and ordinary
transposes, exactly as StageData.epsilon does.
Source: def-sf-verdier-exchange-data, component recipe
(blueprint: lem-pod-verdier-composition-mate-normalization). -/
def exchangeComponent
    (e : LiftedAdjunction ΦX ΦY F G) (o : LiftedAdjunction ΦY ΦX P Q)
    (x : TensorHomData ΦX) (y : TensorHomData ΦY) (omega : Y) (M : X)
    (ax : x.tensor.obj M ⊣ x.hom.obj (op M))
    (ay : y.tensor.obj (F.obj M) ⊣ y.hom.obj (op (F.obj M)))
    (pi : (y.tensor.obj (F.obj M)).obj ((y.hom.obj (op (F.obj M))).obj omega) ≅
      F.obj ((x.tensor.obj M).obj
        (P.obj ((y.hom.obj (op (F.obj M))).obj omega))))
    {omegaX : X} (c : G.obj omega ⟶ omegaX) :
    (y.hom.obj (op (F.obj M))).obj omega ⟶ Q.obj ((x.hom.obj (op M)).obj omegaX) :=
  lastTransposes o x M ax (exceptionalTranspose e o x y omega M ay pi ≫ c)
end Components

end WeilConjectures.VerdierCompositionMate


namespace WeilConjectures.VerdierCompositionMate
open ConstructibleExceptionalCoefficients

end WeilConjectures.VerdierCompositionMate
