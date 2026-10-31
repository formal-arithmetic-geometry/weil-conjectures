/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicRealization.FiniteIntrinsicRealizationComparisons

/-! # Open core of the finite intrinsic projection square

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: lem-sf-finite-intrinsic-projection-open-square-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor finiteIntrinsicDerivedTensor
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  sfIntrinsicDerivedEquivalence CompactSupportFiniteProjection.realization
  sixFunctorFiniteRealization integralCoefficientSheaf integralCoefficientCommRingSheaf
  compactSupportProjectionSquare fixedTensor tensor
  Over.homMk CostructuredArrow.homMk
  sixFunctorFiniteSupport sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
  derivedTensorRightDerivedLowerStar


set_option maxHeartbeats 1600000 in
-- Elaborating the two coefficient tensor presentations requires extra heartbeats.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The local open tensor square, before applying any proper direct image.
Source: fix-prop-projection-formula.proof.md, open tensor step; Stacks 0E8I and 07A4.
(blueprint: lem-sf-finite-intrinsic-projection-open-square-core).

Proof: transpose the intrinsic inverse open tensor map under the open adjunction.
Identify the specified unit by the ordinary conjugate adjunction and exact localization.
The scalar tensor comparison on flat-term K-flat representatives identifies the tensor
part of the transpose, and naturality along resolving isomorphisms extends it to arbitrary
derived inputs. The equivalence triangle identities cancel the units. Injectivity of the
adjunction identifies the inverse maps. The fixed open projection is invertible, so the
intrinsic map is invertible and inverseOnDomain is its inverse. Invert the equation and
use naturality in the two tensor inputs, first along k and then along the arbitrary b.
There is no proper direct image, midpoint, beforeCompositor, or constructibility hypothesis
in this equation. Zero inputs, empty and identity opens and m = 0 satisfy the same formulas. -/
theorem finiteIntrinsicProjectionOpenSquareCore
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (U M : normalizedDVRDerived C.l E X.obj.left m)
    (N : normalizedDVRDerived C.l E c.Z m) (k : U ≅ M)
    (W : DerivedCategory (Sheaf (ProEt.topology c.Z)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1))))))
    (b : (sfIntrinsicDerivedEquivalence c.Z
      (Padic.coefficientExtensionRing C.l E (m + 1))).inverse.obj N ⟶ W) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let Q := compactSupportProjectionSquare f c
    let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
    let RZ := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Q.Z
    let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    let P := finiteDerivedPullback C.l E m c.i
    let Jf := (openImmersionLowerShriek B c.i).mapDerivedCategory
    let Pf := (upperStar B c.i).leftDerivedFunctor
    let tx := Functor.uncurry.obj (derivedTensor B X.obj.left)
    let tz := Functor.uncurry.obj (derivedTensor B c.Z)
    let sx := canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X
    let sz := canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Q.Z
    let ej := FiniteIntrinsicRealization.openComparison (C := C) (E := E) m f c
    let ep := FiniteIntrinsicRealization.inversePullback (C := C) (E := E) m Q.i
    let pj := RZ.inverse.mapIso
      (J.mapIso (k ≪≫ (RX.counitIso.app M).symm) ≪≫ ej.app (RX.inverse.obj M)) ≪≫
        (RZ.unitIso.app _).symm
    sz.hom.app (J.obj U, N) ≫
        RZ.functor.map (tz.map (Prod.mkHom pj.hom b)) ≫
        RZ.functor.map (((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app
          (RX.inverse.obj M)).app W) =
      SystemProjectionFormula.inverseOnDomain
          (SystemProjectionFormula.finiteOpenTensorInv C.l E D C.different c.i
            X.obj.hom (c.g ≫ Y.obj.hom) m U N) ≫
        J.map (sx.hom.app (U, P.obj N)) ≫
        ej.hom.app (tx.obj (RX.inverse.obj U, RX.inverse.obj (P.obj N))) ≫
        RZ.functor.map (Jf.map (tx.map (Prod.mkHom (𝟙 _) (ep.hom.app N)))) ≫
        RZ.functor.map (Jf.map
          (tx.map (Prod.mkHom (RX.inverse.map k.hom) (Pf.map b)))) := by sorry

end WeilConjectures.IntegralProjectionReduction
