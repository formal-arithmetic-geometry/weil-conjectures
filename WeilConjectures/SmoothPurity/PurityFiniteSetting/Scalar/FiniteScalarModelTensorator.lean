/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarDerivedComparison

/-! # The inverse scalar monoidal-model tensorator -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u u₁ u₂
open CategoryTheory CategoryTheory.Abelian MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh
  Functor.leftDerivedFunctorMonoidal Functor.leftDerivedFunctorOplaxMonoidal
  Functor.Monoidal.coreMonoidalTransport Adjunction.leftAdjointUniq

private theorem native_tensorator_transport
    {C : Type u₁} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    {G : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (i : F.leftDerivedFunctor ≅ G) (P Q : _root_.DerivedCategory C) :
    letI : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
    ((Functor.Monoidal.coreMonoidalTransport i).μIso P Q).inv =
      i.inv.app (P ⊗ Q) ≫ (F.leftDerivedTensorComparison.app P).app Q ≫
        (i.hom.app P ⊗ₘ i.hom.app Q) := by
  let : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  rw [Functor.Monoidal.coreMonoidalTransport_μIso_inv]
  rw [Functor.leftDerivedFunctorMonoidal_δ]

-- Generate congruence using syntactic agreement of arguments, rather than asking
-- the kernel to normalize the full concrete localization constructions.
open Lean Meta in
private meta def solveScalarInstanceCongr : Nat → MVarId → MetaM (List MVarId)
  | 0, g => pure [g]
  | n + 1, g => g.withContext do
    let t ← instantiateMVars (← g.getType)
    if t.isForall then
      let (_, g) ← g.intro1
      return ← solveScalarInstanceCongr n g
    let g ← g.eqOfHEq
    let t ← instantiateMVars (← g.getType)
    let some (_, a, _, b) := t.heq? | return [g]
    if a == b then
      g.hrefl
      return []
    if ← g.proofIrrelHeq then return []
    if a.isApp && b.isApp && a.getAppFn == b.getAppFn &&
        a.getAppNumArgs == b.getAppNumArgs then
      let f := a.getAppFn
      let c ← mkHCongrWithArity f a.getAppNumArgs
      let proof ← forallTelescope c.type fun xs t => do
        let proof := mkAppN c.proof xs
        if t.isEq then
          mkLambdaFVars xs (← mkAppM ``heq_of_eq #[proof])
        else
          pure c.proof
      let gs ← g.apply proof
      return (← gs.mapM (solveScalarInstanceCongr n)).flatten
    let a' ← withReducible (whnf a)
    let b' ← withReducible (whnf b)
    if a' != a || b' != b then
      let g ← g.change (← mkHEq a' b')
      return ← solveScalarInstanceCongr n g
    try
      g.hrefl
      return []
    catch _ => return [g]
set_option maxHeartbeats 200000 in
-- Keep the canonical scalar instances separate from the tensor-data record.
/-- The inverse transported tensorator is the canonical comparison followed by the
native left-derived tensor comparison and the tensor of inverse comparisons.
Source: finite reduction of purity, proof Step 2; Stacks 07A4 and 0FPT.
(blueprint: lem-pur-finite-scalar-model-tensorator).
Proof: the abstract transport formula follows from coreMonoidalTransport_μIso_inv
and leftDerivedFunctorMonoidal_δ. Specialize it using the arguments stored in the
actual model. Explicit heterogeneous congruence and proof irrelevance identify its
instance arguments with those of the displayed canonical comparison. HEq retains
the actual object instances. -/
theorem finiteScalar_model_tensorator
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (P Q : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    letI : Algebra A B := φ.toAlgebra
    letI : (ProEtale.sheafExtendScalars φ T).PreservesKFlatQuasiIso :=
      ProEtale.preservesKFlatQuasiIso_sheafExtendScalars A B T
    letI : (ProEtale.sheafExtendScalars φ T).leftDerivedFunctor.Monoidal :=
      (ProEtale.sheafExtendScalars φ T).leftDerivedFunctorMonoidal
    let e := finiteScalarDerivedComparison φ T
    HEq ((finiteScalarMonoidalModel φ T).μIso P Q).inv
      (e.hom.app (P ⊗ Q) ≫
      ((ProEtale.sheafExtendScalars φ T).leftDerivedTensorComparison.app
        P).app Q ≫
      (e.inv.app P ⊗ₘ
        e.inv.app Q)) := by
  dsimp (config := { proj := false }) only
  delta finiteScalarMonoidalModel finiteScalarDerivedComparison
  dsimp (config := { proj := false }) only
  -- Reuse the constructor arguments, including its native monoidal instance.
  -- Reconstructing those instances would force large dependent conversions.
  open Lean Meta Elab Tactic in
  run_tac do
    withMainContext do
      let goal ← getMainGoal
      let target ← instantiateMVars (← goal.getType)
      let lhs := target.getAppArgs[1]!
      let some transport := lhs.find? (fun e ↦
          e.isAppOfArity ``Functor.Monoidal.coreMonoidalTransport 10) |
        throwError "expected the explicit monoidal transport"
      let some tensorator := lhs.find? (fun e ↦
          e.isAppOf ``Functor.CoreMonoidal.μIso && e.getAppNumArgs ≥ 2) |
        throwError "expected the model tensorator"
      let args := tensorator.getAppArgs
      let native := transport.getAppArgs[8]!
      let some native := native.find? (fun e ↦
          e.isAppOf ``Functor.leftDerivedFunctorMonoidal) |
        throwError "expected the native monoidal structure"
      let h ← mkAppOptM ``native_tensorator_transport
        ((native.getAppArgs.map some) ++
          #[none, some transport.getAppArgs[9]!,
            some args[args.size - 2]!, some args[args.size - 1]!])
      let h ← mkAppM ``heq_of_eq #[h]
      let ht ← whnf (← inferType h)
      let ta := target.getAppArgs
      let ha := ht.getAppArgs
      let hl ← mkFreshExprMVar (← mkHEq ta[1]! ha[1]!) .syntheticOpaque
      let hr ← mkFreshExprMVar (← mkHEq ha[3]! ta[3]!) .syntheticOpaque
      let middle ← mkAppM ``HEq.trans #[h, hr]
      let result ← mkAppM ``HEq.trans #[hl, middle]
      goal.assign result
      let left ← solveScalarInstanceCongr 40 hl.mvarId!
      let right ← solveScalarInstanceCongr 40 hr.mvarId!
      replaceMainGoal (left ++ right)

end WeilConjectures.PurityFiniteSetting
