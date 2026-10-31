/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.CanonicalFiniteIntrinsicTensorComparison
public import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionFormulaCoherence
import Mathlib.Lean.Meta.CongrTheorems

/-! # Coordinates between the proper and open projection factors

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56 and 0E8I.
The intermediate comparison is built from tensor, direct image, open extension and
inverse-image realization. It does not use a projection map or its inverse.
(blueprint: def-sf-finite-intrinsic-projection-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates
open CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E]

-- Keep the coefficient equivalence abstract while exposing its derived functor projections.
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicModuleEquivalence

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The proper factor in the published fixed coefficient presentation.
Source: Stacks 0B56 (blueprint: def-sf-finite-intrinsic-projection-coordinates). -/
def fixedProper (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))
  let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
  let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
  RY.functor.map (((rightDerivedLowerStarProjectionMap A c.g).app
    ((openImmersionLowerShriek A c.i).mapDerivedCategory.obj (RX.inverse.obj K.obj))).app
      (RY.inverse.obj L.obj))

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The fixed open factor followed by the fixed inverse-image compositor.
Source: Stacks 0E8I (blueprint: def-sf-finite-intrinsic-projection-coordinates). -/
def fixedTail (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left) :=
  letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let A := ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))
  let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
  let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
  let R := (lowerStar A c.g).rightDerivedFunctor
  let J := (openImmersionLowerShriek A c.i).mapDerivedCategory
  let M := RX.inverse.obj K.obj
  let N := RY.inverse.obj L.obj
  RY.functor.map (R.map
    (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app M).app
      ((upperStar A c.g).leftDerivedFunctor.obj N)) ≫
    R.map (J.map (((derivedTensor A X.obj.left).obj M).map
      ((leftDerivedUpperStarCompactificationIso A c).hom.app N))))

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The explicitly constructed comparison at the junction of the proper and open factors.
It uses no projection map, inverse projection, or existence witness.
Source: coefficient realization and Stacks 07A4, 0B56.
(blueprint: def-sf-finite-intrinsic-projection-coordinates). -/
@[irreducible] def midpoint (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
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
      RY.functor.obj ((lowerStar B c.g).rightDerivedFunctor.obj
        (((derivedTensor B c.Z).obj
          ((openImmersionLowerShriek B c.i).mapDerivedCategory.obj
            (RX.inverse.obj K.obj))).obj
          ((upperStar B c.g).leftDerivedFunctor.obj (RY.inverse.obj L.obj)))) := by
  letI := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let Q := compactSupportProjectionSquare f c
  let RX := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) X
  let RY := realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y
  let RZ := sfIntrinsicDerivedEquivalence c.Z A
  let J := (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
  let P := finiteDerivedPullback C.l E m c.g
  let R := proEtaleConstantDerivedDirectImage c.g A
  let Jf := (openImmersionLowerShriek B c.i).mapDerivedCategory
  let Pf := (upperStar B c.g).leftDerivedFunctor
  let Rf := (lowerStar B c.g).rightDerivedFunctor
  let T := Functor.uncurry.obj (derivedTensor B c.Z)
  let ej : RX.functor ⋙ J ≅ Jf ⋙ RZ.functor := by
    change (sfIntrinsicModuleEquivalence X.obj.left A).functor.mapDerivedCategory ⋙
      (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory ≅
      (openImmersionLowerShriek B c.i).mapDerivedCategory ⋙
        (sfIntrinsicModuleEquivalence c.Z A).functor.mapDerivedCategory
    exact (Functor.mapDerivedCategoryCompIso
      (sfIntrinsicModuleEquivalence X.obj.left A).functor
      (sfIntrinsicExtensionByZero c.i A)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison A c.i) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  let ep : P ≅ RY.inverse ⋙ sfFixedDerivedPullback A c.g ⋙ RZ.functor := by
    change (sfIntrinsicPullback A c.g).mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence Y.obj.left A).inverse.mapDerivedCategory ⋙
        sfFixedDerivedPullback A c.g ⋙
          (sfIntrinsicModuleEquivalence c.Z A).functor.mapDerivedCategory
    exact Functor.mapDerivedCategoryCompIso
        (sfIntrinsicModuleEquivalence Y.obj.left A).inverse
        ((upperStar B c.g) ⋙ (sfIntrinsicModuleEquivalence c.Z A).functor) ≪≫
          Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
  let pj : RZ.inverse.obj (J.obj U) ≅ Jf.obj (RX.inverse.obj K.obj) :=
    RZ.inverse.mapIso (J.mapIso (k ≪≫ (RX.counitIso.app K.obj).symm) ≪≫
      ej.app (RX.inverse.obj K.obj)) ≪≫ (RZ.unitIso.app _).symm
  let pp : RZ.inverse.obj (P.obj V) ≅ Pf.obj (RY.inverse.obj L.obj) :=
    RZ.inverse.mapIso (P.mapIso l ≪≫ ep.app L.obj ≪≫
      RZ.functor.mapIso ((leftDerivedUpperStarIsoMapDerivedCategory B c.g).symm.app
        (RY.inverse.obj L.obj))) ≪≫ (RZ.unitIso.app _).symm
  exact R.map ((canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Q.Z).hom.app
      (J.obj U, P.obj V)) ≫
    (sfIntrinsicDerivedDirectImageComparison c.g A).hom.app
      (T.obj (RZ.inverse.obj (J.obj U), RZ.inverse.obj (P.obj V))) ≫
    RY.functor.map (Rf.map (T.map (Prod.mkHom pj.hom pp.hom)))

attribute [local irreducible] sfIntrinsicDerivedEquivalence
  Functor.mapDerivedCategory Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor projectionMapOfCompactification
  rightDerivedLowerStarProjectionMap derivedOpenImmersionLowerShriekProjectionIso
  leftDerivedUpperStarCompactificationIso projectionTensorCoordinateComponent

/- As in FiniteProjectionFromDescent, factor congruence across the argument boundaries
of definitionally equal coefficient instances, caching repeated equalities. This builds
ordinary equality proofs checked by the kernel and keeps the derived functors abstract. -/
private meta def coefficientInstanceCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "congruence recursion limit"
  | fuel + 1 =>
    let (_, g) ← g.intros
    g.withContext do
      let t ← Lean.instantiateMVars (← g.getType)
      let entries ← cache.get
      if let some pf := entries[t]? then
        g.assign pf
        return
      let (a, b) ← if let some (_, a, b) := t.eq? then pure (a, b)
        else if let some (_, a, _, b) := t.heq? then pure (a, b)
        else throwError "unexpected congruence goal {t}"
      let a := a.consumeMData
      let b := b.consumeMData
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else
        let a ← match a with
          | .letE .. => Lean.Meta.whnf a
          | _ => if a.getAppFn.isConstOf ``CategoryTheory.Functor.obj then
              Lean.Meta.whnf a else pure a
        let b ← match b with
          | .letE .. => Lean.Meta.whnf b
          | _ => if b.getAppFn.isConstOf ``CategoryTheory.Functor.obj then
              Lean.Meta.whnf b else pure b
        if a == b then
          if t.isHEq then g.hrefl else g.refl
        else if ← g.proofIrrelHeq then pure ()
        else if t.isEq then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
            { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else if a.getAppFn == b.getAppFn &&
            a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
          let f := a.getAppFn
          let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
          let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
          let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
            (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
          let gs ← g.apply (c.proof.beta #[f]) { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else
          if t.isHEq then g.hrefl else g.refl
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)

private theorem map_projection_factors
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [ProEtale.UpperStarPreservesFlat B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {A : Type*} [Category A] (F : DerivedCategory (Sheaf (ProEt.topology Y) B) ⥤ A)
    (M : DerivedCategory (Sheaf (ProEt.topology X) B))
    (N : DerivedCategory (Sheaf (ProEt.topology Y) B)) :
    F.map (((rightDerivedLowerStarProjectionMap B c.g).app
      ((openImmersionLowerShriek B c.i).mapDerivedCategory.obj M)).app N) ≫
      F.map ((lowerStar B c.g).rightDerivedFunctor.map
        (((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app M).app
          ((upperStar B c.g).leftDerivedFunctor.obj N)) ≫
        (lowerStar B c.g).rightDerivedFunctor.map
          ((openImmersionLowerShriek B c.i).mapDerivedCategory.map
            (((derivedTensor B X).obj M).map
              ((leftDerivedUpperStarCompactificationIso B c).hom.app N)))) =
    F.map (projectionTensorCoordinateComponent B c M N) := by
  rw [projectionTensorCoordinateComponent_eq, projectionMapOfCompactification_app_app]
  exact (F.map_comp _ _).symm

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The two fixed factors are the published fixed projection.
Source: the definition of projectionMapOfCompactification.
(blueprint: def-sf-finite-intrinsic-projection-coordinates). -/
theorem fixed_factorization (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left) :
    fixedProper m f c K L ≫ fixedTail m f c K L =
      (realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y).functor.map
        (fixedComponent (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) f c
          ((realization (C := C) (E := E) (n := m + 1)
            (hn := Nat.le_add_left 1 m) X).inverse.obj K.obj)
          ((realization (C := C) (E := E) (n := m + 1)
            (hn := Nat.le_add_left 1 m) Y).inverse.obj L.obj)) := by
  dsimp only [fixedProper, fixedTail, fixedComponent]
  have result := map_projection_factors
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (m + 1)))) c
    (realization (C := C) (E := E) (n := m + 1) (hn := Nat.le_add_left 1 m) Y).functor
    ((realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) X).inverse.obj K.obj)
    ((realization (C := C) (E := E) (n := m + 1)
      (hn := Nat.le_add_left 1 m) Y).inverse.obj L.obj)
  run_tac Lean.Elab.Tactic.withMainContext do
    let some r := (← Lean.getLCtx).findFromUserName? `result |
      throwError "missing fixed factorization"
    let g ← Lean.Elab.Tactic.getMainGoal
    let src ← Lean.Meta.inferType r.toExpr
    let tgt ← g.getType
    let v ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq src tgt)
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[v, r.toExpr])
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    coefficientInstanceCongr cache 100 v.mvarId!
    Lean.Elab.Tactic.replaceMainGoal []

private theorem assoc_four {A : Type*} [Category A] {P Q R S T : A}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (d : S ⟶ T) :
    a ≫ (b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- Including the constructible component exposes exactly the two fixed factors.
Source: the definition of the constructible conjugate.
(blueprint: def-sf-finite-intrinsic-projection-coordinates). -/
theorem component_factorization (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left) :
    (finiteInclusion (C := C) (E := E) m Y).map (component S f c K L) =
      (sourceComparison S f c K L).hom ≫ fixedProper m f c K L ≫
        fixedTail m f c K L ≫ (targetComparison S f c K L).inv := by
  change (sourceComparison S f c K L).hom ≫ _ ≫
    (targetComparison S f c K L).inv = _
  rw [← fixed_factorization m f c K L]
  exact assoc_four _ _ _ _

end WeilConjectures.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates
