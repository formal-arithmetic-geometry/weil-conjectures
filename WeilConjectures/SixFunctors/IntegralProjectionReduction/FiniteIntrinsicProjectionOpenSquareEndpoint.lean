/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicRealization.FiniteIntrinsicRealizationComparisons

/-! # Endpoint of the finite intrinsic open square

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: def-sf-finite-intrinsic-projection-open-square-endpoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The common endpoint used by the two independent halves of the open square.
Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: def-sf-finite-intrinsic-projection-open-square-endpoint).

This is the coefficient realization of the open inverse tensor coordinate followed by
its fixed tensor and direct-image comparison. It contains no equality proof and no
choice of a witness. -/
@[irreducible] def finiteIntrinsicProjectionOpenSquareEndpoint
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
    let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
    (proEtaleConstantDerivedDirectImage c.g A).obj
      ((finiteIntrinsicDerivedTensor C.l E c.Z m).obj
        (((sfIntrinsicExtensionByZero c.i A).mapDerivedCategory).obj U,
          (finiteDerivedPullback C.l E m c.g).obj V)) ⟶
      RY.functor.obj ((sfFixedCompactSupport A c).obj
        (((derivedTensor B X.obj.left).obj (RX.inverse.obj K.obj)).obj
          ((upperStar B c.i).leftDerivedFunctor.obj
            ((upperStar B c.g).leftDerivedFunctor.obj (RY.inverse.obj L.obj))))) := by
  letI := SystemProjectionFormula.residueInvertible C.l D C.different X.obj.left X.obj.hom
  letI := SystemProjectionFormula.residueInvertible C.l D C.different c.Z (c.g ≫ Y.obj.hom)
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let Q := compactSupportProjectionSquare f c
  let RX := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) X
  let RY := realization (C := C) (E := E) (n := m + 1)
    (hn := Nat.le_add_left 1 m) Y
  let RZ := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Q.Z
  let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
  let P := finiteDerivedPullback C.l E m c.i
  let Pg := finiteDerivedPullback C.l E m c.g
  let Jf := (openImmersionLowerShriek B c.i).mapDerivedCategory
  let Pf := (upperStar B c.i).leftDerivedFunctor
  let tx := Functor.uncurry.obj (derivedTensor B X.obj.left)
  let N := Pg.obj V
  let v := SystemProjectionFormula.finiteOpenTensorInv C.l E D C.different c.i
    X.obj.hom (c.g ≫ Y.obj.hom) m U N
  let sx := canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X
  let eJ := FiniteIntrinsicRealization.openComparison (C := C) (E := E) m f c
  let ep := FiniteIntrinsicRealization.inversePullback (C := C) (E := E) m Q.i
  let ak := RX.inverse.map k.hom
  let epg : Pg ≅ RY.inverse ⋙ sfFixedDerivedPullback A c.g ⋙ RZ.functor := by
    change (sfIntrinsicPullback A c.g).mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence Y.obj.left A).inverse.mapDerivedCategory ⋙
        sfFixedDerivedPullback A c.g ⋙
          (sfIntrinsicModuleEquivalence c.Z A).functor.mapDerivedCategory
    exact Functor.mapDerivedCategoryCompIso
        (sfIntrinsicModuleEquivalence Y.obj.left A).inverse
        ((upperStar B c.g) ⋙ (sfIntrinsicModuleEquivalence c.Z A).functor) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
  let pp := RZ.inverse.mapIso (Pg.mapIso l ≪≫ epg.app L.obj ≪≫
    RZ.functor.mapIso ((leftDerivedUpperStarIsoMapDerivedCategory B c.g).symm.app
      (RY.inverse.obj L.obj))) ≪≫ (RZ.unitIso.app _).symm
  let R := proEtaleConstantDerivedDirectImage c.g A
  let er := sfIntrinsicDerivedDirectImageComparison c.g A
  exact R.map ((SystemProjectionFormula.inverseOnDomain v ≫ J.map (sx.hom.app (U, P.obj N)) ≫
      eJ.hom.app (tx.obj (RX.inverse.obj U, RX.inverse.obj (P.obj N))) ≫
      RZ.functor.map (Jf.map (tx.map (Prod.mkHom (𝟙 _) (ep.hom.app N))))) ≫
      RZ.functor.map (Jf.map (tx.map (Prod.mkHom ak (Pf.map pp.hom))))) ≫
    er.hom.app (Jf.obj (tx.obj (RX.inverse.obj K.obj,
      Pf.obj ((upperStar B c.g).leftDerivedFunctor.obj (RY.inverse.obj L.obj)))))

end WeilConjectures.IntegralProjectionReduction
