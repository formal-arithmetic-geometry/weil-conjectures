/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionCoordinates
import all WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionCoordinates

/-! # Coordinates after the open tensor comparison

Source: fix-prop-projection-formula.proof.md, same-map sentence; Stacks 0E8I, 0D6D.
(blueprint: def-sf-finite-intrinsic-projection-open-coordinates).
The junction uses only tensor and realization isomorphisms, with no projection map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates
open CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E]

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicModuleEquivalence

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- Cancel the coefficient realization in a single inverse image, using exact descent
and the published exact/K-flat comparison. Source: Stacks 0D6D
(blueprint: def-sf-finite-intrinsic-projection-open-coordinates). -/
def pullCoordinate (m : ℕ) {X Y : Scheme.{u}} (p : X ⟶ Y)
    (V : normalizedDVRDerived C.l E Y m) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    (sfIntrinsicDerivedEquivalence X A).inverse.obj
        ((finiteDerivedPullback C.l E m p).obj V) ≅
      (upperStar B p).leftDerivedFunctor.obj
        ((sfIntrinsicDerivedEquivalence Y A).inverse.obj V) := by
  letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let RX := sfIntrinsicDerivedEquivalence X A
  let RY := sfIntrinsicDerivedEquivalence Y A
  let P := finiteDerivedPullback C.l E m p
  let ep : P ≅ RY.inverse ⋙ sfFixedDerivedPullback A p ⋙ RX.functor := by
    change (sfIntrinsicPullback A p).mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence Y A).inverse.mapDerivedCategory ⋙
        sfFixedDerivedPullback A p ⋙
          (sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory
    exact Functor.mapDerivedCategoryCompIso
        (sfIntrinsicModuleEquivalence Y A).inverse
        ((upperStar B p) ⋙ (sfIntrinsicModuleEquivalence X A).functor) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
  exact RX.inverse.mapIso (ep.app V ≪≫
    RX.functor.mapIso ((leftDerivedUpperStarIsoMapDerivedCategory B p).symm.app
      (RY.inverse.obj V))) ≪≫ (RX.unitIso.app _).symm

attribute [local irreducible] sfIntrinsicDerivedEquivalence
  derivedOpenImmersionLowerShriekProjectionIso leftDerivedUpperStarCompactificationIso

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The fixed open projection factor, before composing the two inverse images.
Source: Stacks 0E8I
(blueprint: def-sf-finite-intrinsic-projection-open-coordinates). -/
def fixedOpenPart (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
    let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
    let J := (openImmersionLowerShriek B c.i).mapDerivedCategory
    let R := (lowerStar B c.g).rightDerivedFunctor
    let M := RX.inverse.obj K.obj
    let N := (upperStar B c.g).leftDerivedFunctor.obj (RY.inverse.obj L.obj)
    RY.functor.obj (R.obj (((derivedTensor B c.Z).obj (J.obj M)).obj N)) ⟶
      RY.functor.obj (R.obj (J.obj (((derivedTensor B X.obj.left).obj M).obj
        ((upperStar B c.i).leftDerivedFunctor.obj N)))) := by
  letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))
  let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
  let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
  exact RY.functor.map ((lowerStar B c.g).rightDerivedFunctor.map
    (((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app
      (RX.inverse.obj K.obj)).app
      ((upperStar B c.g).leftDerivedFunctor.obj (RY.inverse.obj L.obj))))

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The fixed inverse-image compositor, after the open projection factor.
Source: Stacks 0D6D
(blueprint: def-sf-finite-intrinsic-projection-open-coordinates). -/
def fixedCompositorPart (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
    let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
    let J := (openImmersionLowerShriek B c.i).mapDerivedCategory
    let R := (lowerStar B c.g).rightDerivedFunctor
    let M := RX.inverse.obj K.obj
    let N := RY.inverse.obj L.obj
    RY.functor.obj (R.obj (J.obj (((derivedTensor B X.obj.left).obj M).obj
        ((upperStar B c.i).leftDerivedFunctor.obj
          ((upperStar B c.g).leftDerivedFunctor.obj N))))) ⟶
      RY.functor.obj (R.obj (J.obj (((derivedTensor B X.obj.left).obj M).obj
        ((upperStar B f.hom.left).leftDerivedFunctor.obj N)))) := by
  letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))
  let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
  let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
  exact RY.functor.map ((lowerStar B c.g).rightDerivedFunctor.map
    ((openImmersionLowerShriek B c.i).mapDerivedCategory.map
      (((derivedTensor B X.obj.left).obj (RX.inverse.obj K.obj)).map
        ((leftDerivedUpperStarCompactificationIso B c).hom.app (RY.inverse.obj L.obj)))))

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- Functoriality separates the open comparison and the pullback compositor.
Source: the definition of fixedTail.
(blueprint: def-sf-finite-intrinsic-projection-open-coordinates). -/
theorem fixedTail_parts (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left) :
    fixedTail m f c K L =
      fixedOpenPart m f c K L ≫ fixedCompositorPart m f c K L := by
  dsimp only [fixedTail, fixedOpenPart, fixedCompositorPart]
  run_tac Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.instantiateMVars (← g.getType)
    let some (_, lhs, _) := t.eq? | throwError "expected equality"
    let args := lhs.getAppArgs
    let comp := args[7]!
    let ca := comp.getAppArgs
    -- Reuse the goal's coefficient data so kernel conversion stays structural.
    let pf := Lean.mkAppN
      (Lean.mkConst ``CategoryTheory.Functor.map_comp lhs.getAppFn.constLevels!)
      (args[:5].toArray ++ ca[2:5].toArray ++ #[ca[5]!, ca[6]!])
    let src ← Lean.Meta.inferType pf
    let v ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq src t)
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[v, pf])
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    coefficientInstanceCongr cache 100 v.mvarId!
    Lean.Elab.Tactic.replaceMainGoal []
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The comparison after open tensor and before inverse-image composition. It is built
from the tensor comparison, support realization and the two unary pullback coordinates.
Source: Stacks 0E8I, 0D6D
(blueprint: def-sf-finite-intrinsic-projection-open-coordinates). -/
@[irreducible] def beforeCompositor (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
    let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
    (sfAmbientCompactSupportCandidate A c).obj
      ((finiteIntrinsicDerivedTensor C.l E X.obj.left m).obj
        (U, (finiteDerivedPullback C.l E m c.i).obj
          ((finiteDerivedPullback C.l E m c.g).obj V))) ⟶
      RY.functor.obj ((sfFixedCompactSupport A c).obj
        (((derivedTensor B X.obj.left).obj (RX.inverse.obj K.obj)).obj
          ((upperStar B c.i).leftDerivedFunctor.obj
            ((upperStar B c.g).leftDerivedFunctor.obj (RY.inverse.obj L.obj))))) := by
  letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
  let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
  let RZ := sfIntrinsicDerivedEquivalence c.Z A
  let P := finiteDerivedPullback C.l E m c.g
  let Q := finiteDerivedPullback C.l E m c.i
  let Qf := (upperStar B c.i).leftDerivedFunctor
  let F := sfAmbientCompactSupportCandidate A c
  let Ff := sfFixedCompactSupport A c
  let T := Functor.uncurry.obj (derivedTensor B X.obj.left)
  let W := Q.obj (P.obj V)
  let p := pullCoordinate (C := C) (E := E) m c.i (P.obj V) ≪≫
    Qf.mapIso (RZ.inverse.mapIso (P.mapIso l) ≪≫
      pullCoordinate (C := C) (E := E) m c.g L.obj)
  exact F.map ((canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X).hom.app
      (U, W)) ≫
    (sfIntrinsicCompactSupportComparison A c).hom.app
      (T.obj (RX.inverse.obj U, RX.inverse.obj W)) ≫
    RY.functor.map (Ff.map (T.map (Prod.mkHom (RX.inverse.map k.hom) p.hom)))

end WeilConjectures.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates
