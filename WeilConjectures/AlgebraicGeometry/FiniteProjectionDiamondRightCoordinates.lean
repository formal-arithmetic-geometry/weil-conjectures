/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeCoordinates
import Mathlib.Lean.Meta.CongrTheorems

/-! # Fixed-scalar coordinates of the right projection diamond

The definition is compared with the exposed fixed-category tensor and projection API.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true


universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
open CompactSupportFiniteProjection

-- Match the exposed functor and morphism coordinates without unfolding derived constructions.
attribute [local irreducible] AlgebraicGeometry.ProEtale.derivedTensor
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.leftDerivedFunctor
attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local irreducible] leftDerivedUpperStarTensorIso projectionMapOfCompactification
  rightDerivedLowerShriekOfCompactificationBaseChangeMap


-- Compare coordinate expressions at each argument boundary, caching repeated instance
-- equalities instead of unfolding the underlying derived constructions.
private meta def coordinateHead (fuel : Nat) (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e := e.consumeMData
    let names := [``FiniteProjectionExchange.mu, ``FiniteProjectionExchange.pf,
      ``FiniteProjectionExchange.pull, ``sfFixedCompactSupport,
      ``rightDerivedLowerShriekOfCompactification, ``projectionTensorCoordinateComponent]
    if names.any e.getAppFn.isConstOf then
      if let some e' ← Lean.Meta.unfoldDefinition? e then
        return ← coordinateHead fuel e'
    match e with
    | .letE .. => return ← coordinateHead fuel (← Lean.Meta.whnf e)
    | _ =>
      if e.getAppFn.isConstOf ``CategoryTheory.Functor.obj then
        return ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e)
      return e

private meta def coordinateCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "coordinate congruence recursion limit"
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
      let a ← coordinateHead 20 a
      let b ← coordinateHead 20 b
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else if ← g.proofIrrelHeq then pure ()
      else if t.isEq then
        let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
          { synthAssignedInstances := false }
        for g in gs do coordinateCongr cache fuel g
      else if a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
        let f := a.getAppFn
        let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
        let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
        let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
          (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
        let gs ← g.apply (c.proof.beta #[f]) { synthAssignedInstances := false }
        for g in gs do coordinateCongr cache fuel g
      else
        if t.isHEq then g.hrefl else g.refl
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Fixed-category coordinates of the right diamond, for arbitrary derived inputs.
Source: prop-sf-pf-coherence.proof.md, displayed right-diamond composite.
(blueprint: lem-sf-finite-projection-diamond-right-fixed-coordinates).

Proof: unfold `diamondRight` and `tensorMap`. Functoriality sends the identity
in the second tensor argument to an identity, which cancels. The tensor comparison
is the published `leftDerivedUpperStarTensorIso`. The compactly supported functor
is the open/proper composite defining `sfFixedCompactSupport`; the pullbacks are
`fixedDerivedPull`. Finally `projectionTensorCoordinateComponent_eq` identifies
the last factor with `fixedComponent`. These substitutions give the displayed
three factors. No constructibility, finite-Tor, or invertibility of exchange or
projection is used.
-/
theorem finiteProjectionDiamondRight_fixed_coordinates
    (Q : SixFunctorCompactifiedSquare D)
    (K : DerivedCategory (Sheaf (ProEt.topology Q.X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (L : DerivedCategory (Sheaf (ProEt.topology Q.Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    FiniteProjectionExchange.diamondRight A Q.square Q.compactification K L =
      (leftDerivedUpperStarTensorIso (ModuleCat A) Q.g.hom.left
        ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n)
          Q.compactification).obj K) L).hom ≫
        ((fixedTensor (C := C) (E := E) (n := n) Q.Y').map
          (FiniteProjectionExchange.ex A Q.square Q.compactification K)).app
          ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g).obj L) ≫
        fixedComponent (C := C) (E := E) (n := n) (hn := hn) Q.f'
          (Q.compactification.ofIsPullback Q.square)
          ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g').obj K)
          ((fixedDerivedPull (C := C) (E := E) (n := n) Q.g).obj L) := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  dsimp only
  dsimp only [fixedTensor, fixedDerivedPull, fixedComponent]
  unfold FiniteProjectionExchange.diamondRight FiniteProjectionExchange.tensorMap
  conv_lhs =>
    arg 2
    arg 1
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  run_tac Lean.Elab.Tactic.withMainContext do
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    coordinateCongr cache 100 (← Lean.Elab.Tactic.getMainGoal)
    Lean.Elab.Tactic.replaceMainGoal []

end WeilConjectures
