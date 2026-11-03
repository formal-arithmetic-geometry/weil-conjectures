/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionTensorMate.CondensedBridge.CompositionTensorMateData2
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.ChartFactors.ChartDncVectorFactorData
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleSourceTransport
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import all Mathlib.CategoryTheory.Adjunction.Mates
import all Mathlib.Logic.Function.Basic
import all WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.Tensor.TensorMateEtalePrecomp
import all WeilConjectures.AlgebraicGeometry.EtaleSupportExchange.EtaleSupportExchangeRightMate

/-! # Exceptional adjunctions in finite coefficient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CompositionTensorMate

attribute [local irreducible] ProEtale.originCompositionAmbient
  ProEtale.fixedCompactSupportComparisonIso ProEtale.compactSupportSiteComparison
  Etale.unboundedEtaleLowerShriekCompIso Etale.rightDerivedLowerShriekPlusCompIso
  standingExceptionalHomEquiv

universe v w

private theorem coefficientPiHEq {α β : Sort v} {F : α → Sort w} {G : β → Sort w}
    (h : α = β) (hFG : HEq F G) : HEq ((x : α) → F x) ((x : β) → G x) := by
  cases h
  cases hFG
  rfl

private theorem coefficientInferInstanceHEq {α : Sort v} (a : α) :
    HEq (@inferInstance α a) a := by
  rfl

private theorem coefficientFullSubcategoryObjHEq {C : Type v} [CategoryTheory.Category.{w} C]
    {P : CategoryTheory.ObjectProperty C}
    (X : C) (hX : P X) :
    HEq ((⟨X, hX⟩ : P.FullSubcategory).obj) X := by
  rfl

meta section

private def coefficientInstanceNormalize (e : Lean.Expr) (fuel : Nat) :
    Lean.Meta.MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e := e.consumeMData
    if e.isAppOf ``DFunLike.coe then
      let args := e.getAppArgs
      if args.size > 4 && args[0]!.isAppOf ``Equiv then
        let equiv ← coefficientInstanceNormalize args[4]! fuel
        let equiv ← if equiv.isAppOf ``Equiv.trans then do
          let expanded ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? equiv)
          pure (expanded.getD equiv)
        else pure equiv
        let e' := Lean.mkAppN (.proj ``Equiv 0 equiv) (args.extract 5 args.size)
        let e' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e')
        return ← coefficientInstanceNormalize e' fuel
    if e.isAppOf ``CategoryTheory.Functor.obj then
      let args := e.getAppArgs
      if args.size > 4 then
        let f ← coefficientInstanceNormalize args[4]! fuel
        if f != args[4]! || f.isAppOf ``CategoryTheory.Functor.comp ||
            f.isAppOf ``CategoryTheory.Functor.mk ||
            f.isAppOf ``CategoryTheory.ObjectProperty.ι then
          let e := Lean.mkAppN e.getAppFn (args.set! 4 f)
          let e ← Lean.Meta.withTransparency .default (Lean.Meta.whnf e)
          return ← coefficientInstanceNormalize e fuel
    if e.isAppOf ``Function.comp ||
        e.isAppOf ``AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification ||
        e.isAppOf ``AlgebraicGeometry.ProEtale.rightDerivedLowerShriek ||
        e.isAppOf ``EquivLike.toFunLike ||
        e.isAppOf ``CategoryTheory.Functor.comp ||
        e.isAppOf ``CategoryTheory.ObjectProperty.ι ||
        e.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory.mk ||
        e.isAppOf ``CommRing.toRing ||
        e.isAppOf ``AlgebraicGeometry.ProEtale.CompositionTensorMate.D ||
        e.isAppOf ``AlgebraicGeometry.ProEtale.CompositionTensorMate.F ||
        e.isAppOf ``AlgebraicGeometry.ProEtale.CompositionTensorMate.G ||
        e.isAppOf ``ConstantScalarRestriction.fixedAbelian ||
        e.isAppOf ``ULift.commRing || e.isAppOf ``ULift.ring ||
        e.isAppOf ``AlgebraicGeometry.Etale.cartierAbelianEtale ||
        e.isAppOf ``AlgebraicGeometry.Etale.cartierAbelianPro ||
        e.isAppOf ``WeilConjectures.PurityFiniteSetting.chartCoefficientUnit ||
        e.isAppOf ``WeilConjectures.PurityFiniteSetting.diagonalOrdinaryDualizing ||
        e.isAppOf ``WeilConjectures.PurityFiniteSetting.ChartComparisons.composition ||
        e.isAppOf ``AlgebraicGeometry.ProEtale.standingExceptionalComposition then
      if let some e ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e) then
        return ← coefficientInstanceNormalize e fuel
    match e with
    | .proj n i x =>
      if n == ``CategoryTheory.Functor then
        let x ← coefficientInstanceNormalize x fuel
        let x ← if x.isAppOf ``AlgebraicGeometry.ProEtale.rightDerivedUpperShriek then do
          let expanded ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? x)
          pure (expanded.getD x)
        else pure x
        let e' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf (.proj n i x))
        if e' != e then coefficientInstanceNormalize e' fuel else pure e
      else if n == ``CommRing || n == ``DFunLike || n == ``EquivLike then
        Lean.Meta.withTransparency .default (Lean.Meta.whnf e)
      else return e
    | .letE _ _ v b _ => coefficientInstanceNormalize (b.instantiate1 v) fuel
    | .fvar id =>
      match (← Lean.getLCtx).get! id |>.value? (allowNondep := true) with
      | some v =>
        modifyThe Lean.Meta.State fun s ↦
          { s with zetaDeltaFVarIds := s.zetaDeltaFVarIds.insert id }
        coefficientInstanceNormalize v fuel
      | none => return e
    | .app f a =>
      let f ← coefficientInstanceNormalize f fuel
      let b := (Lean.mkApp f a).headBeta
      if b != e then coefficientInstanceNormalize b fuel else return e
    | _ => return e

private def coefficientInstanceHEq (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (a b : Lean.Expr) (fuel : Nat) : Lean.Meta.MetaM Lean.Expr := do
  let a ← Lean.instantiateMVars a
  let b ← Lean.instantiateMVars b
  if let some h := (← cache.get).get? (a, b) then return h
  let compute (_ : Unit) : Lean.Meta.MetaM Lean.Expr := do
    match fuel with
    | 0 => throwError "structural congruence fuel exhausted"
    | fuel + 1 =>
      let a ← Lean.instantiateMVars a
      let b ← Lean.instantiateMVars b
      if a == b then return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      let a ← coefficientInstanceNormalize a 100
      let b ← coefficientInstanceNormalize b 100
      if a == b then return ← Lean.Meta.mkHEqRefl a
      let isGuarded (e : Lean.Expr) : Bool :=
        e.isAppOf ``AlgebraicGeometry.ProEtale.CompositionTensorMate.c ||
          e.isAppOf ``AlgebraicGeometry.ProEtale.CompositionTensorMate.alpha ||
          e.isAppOf ``AlgebraicGeometry.ProEtale.CompositionTensorMate.epsilon
      if a.getAppFn != b.getAppFn then
        if isGuarded a then
          let expanded ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? a)
          if let some x := expanded then return ← coefficientInstanceHEq cache x b fuel
        if isGuarded b then
          let expanded ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? b)
          if let some x := expanded then return ← coefficientInstanceHEq cache a x fuel
      let reduceGuard (e : Lean.Expr) : Lean.Meta.MetaM
          (Option (Lean.Expr × Lean.Expr)) := do
        unless e.isAppOf ``dite do return none
        let args := e.getAppArgs
        let goal ← Lean.Meta.mkFreshExprMVar args[1]!
        unless ← goal.mvarId!.assumptionCore do return none
        let proof ← Lean.instantiateMVars goal
        let value := (Lean.mkApp args[3]! proof).headBeta
        let h ← Lean.Meta.mkAppOptM ``dif_pos
          #[some args[1]!, some args[2]!, some proof, some args[0]!,
            some args[3]!, some args[4]!]
        unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType h) (← Lean.Meta.mkEq e value) do
          throwError "guard equality did not match"
        let h ← Lean.instantiateMVars h
        return some (value, ← Lean.Meta.mkAppM ``heq_of_eq #[h])
      if let some (x, h) ← reduceGuard a then
        return ← Lean.Meta.mkAppM ``HEq.trans
          #[h, ← coefficientInstanceHEq cache x b fuel]
      if let some (x, h) ← reduceGuard b then
        let h ← Lean.Meta.mkAppM ``HEq.symm #[h]
        return ← Lean.Meta.mkAppM ``HEq.trans
          #[← coefficientInstanceHEq cache a x fuel, h]
      let isExceptionalObject (e : Lean.Expr) : Bool :=
        e.isAppOf ``CategoryTheory.Functor.obj && e.getAppArgs.size > 4 &&
          e.getAppArgs[4]!.isAppOf ``AlgebraicGeometry.ProEtale.rightDerivedUpperShriek
      let expandExceptionalObject (e : Lean.Expr) : Lean.Meta.MetaM Lean.Expr := do
        let args := e.getAppArgs
        let f ← Lean.Meta.withTransparency .all
          (Lean.Meta.unfoldDefinition? args[4]!)
        let e := Lean.mkAppN e.getAppFn (args.set! 4 (f.getD args[4]!))
        Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e)
      if isExceptionalObject a && !isExceptionalObject b then
        return ← coefficientInstanceHEq cache (← expandExceptionalObject a) b fuel
      if isExceptionalObject b && !isExceptionalObject a then
        return ← coefficientInstanceHEq cache a (← expandExceptionalObject b) fuel
      if a.isAppOf ``inferInstance then
        let x := a.getAppArgs.back!
        let h ← Lean.Meta.mkAppM ``coefficientInferInstanceHEq #[x]
        let h' ← coefficientInstanceHEq cache x b fuel
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      if b.isAppOf ``inferInstance then
        let x := b.getAppArgs.back!
        let h ← coefficientInstanceHEq cache a x fuel
        let h' ← Lean.Meta.mkAppM ``coefficientInferInstanceHEq #[x]
        let h' ← Lean.Meta.mkAppM ``HEq.symm #[h']
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      let project (e : Lean.Expr) : Lean.Meta.MetaM (Option (Lean.Expr × Lean.Expr)) := do
        let value? := if e.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory.obj then
          some e.getAppArgs.back!
        else match e with
          | .proj n 0 x =>
            if n == ``CategoryTheory.ObjectProperty.FullSubcategory then some x else none
          | _ => none
        let some value := value? | return none
        let value ← coefficientInstanceNormalize value 100
        unless value.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory.mk do return none
        let args := value.getAppArgs
        let x := args[args.size - 2]!
        let h ← Lean.Meta.mkAppM ``coefficientFullSubcategoryObjHEq #[x, args.back!]
        return some (x, h)
      if let some (x, h) ← project a then
        let h' ← coefficientInstanceHEq cache x b fuel
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      if let some (x, h') ← project b then
        let h ← coefficientInstanceHEq cache a x fuel
        let h' ← Lean.Meta.mkAppM ``HEq.symm #[h']
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      match a, b with
      | .lam _ ta _ _, .lam _ tb _ _ =>
        let hdom ← Lean.Meta.mkAppM ``eq_of_heq #[← coefficientInstanceHEq cache ta tb fuel]
        let g ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkAppM ``HEq #[a, b])
        let gs ← g.mvarId!.apply
          (← Lean.Meta.mkConstWithFreshMVarLevels ``Function.hfunext)
        unless gs.length == 2 do throwError "unexpected hfunext goals"
        gs[0]!.assign hdom
        let (_, g1) ← gs[1]!.intro1
        let (_, g2) ← g1.intro1
        let (h, g3) ← g2.intro1
        for c in ← g3.cases h do
          c.mvarId.withContext do
            let t ← c.mvarId.getType
            let args := t.getAppArgs
            unless args.size == 4 do throwError "expected HEq after hfunext"
            c.mvarId.assign (← coefficientInstanceHEq cache args[1]! args[3]! fuel)
        return ← Lean.instantiateMVars g
      | .forallE n ta ab bi, .forallE n' tb bb bi' =>
        let hdom ← Lean.Meta.mkAppM ``eq_of_heq #[← coefficientInstanceHEq cache ta tb fuel]
        let hf ← coefficientInstanceHEq cache (.lam n ta ab bi) (.lam n' tb bb bi') fuel
        return ← Lean.Meta.mkAppM ``coefficientPiHEq #[hdom, hf]
      | _, _ => pure ()
      let af := a.getAppFn
      let bf := b.getAppFn
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      let sharedType := af.isConstOf ``DerivedCategory ||
        af.isConstOf ``instCategoryDerivedCategory || af.isConstOf ``Sheaf ||
        af.isConstOf ``CategoryTheory.ObjectProperty.FullSubcategory.category ||
        af.isConstOf ``CategoryTheory.Functor.category ||
        af.isConstOf ``CategoryTheory.Functor ||
        af.isConstOf ``HasDerivedCategory.ofIsGrothendieckAbelian
      if sharedType then
        if ← Lean.Meta.withTransparency .reducible (Lean.Meta.isDefEq a b) then
          return ← Lean.Meta.mkHEqRefl a
      if let .proj n i x := af then
        if let .proj m j y := bf then
          if n == m && i == j && aa.size == ba.size then
            let hx ← coefficientInstanceHEq cache x y fuel
            let ex ← Lean.Meta.mkAppM ``eq_of_heq #[hx]
            let tx ← Lean.Meta.inferType x
            let fn := Lean.Expr.lam `value tx (.proj n i (.bvar 0)) .default
            let eh ← Lean.Meta.mkAppM ``congrArg #[fn, ex]
            let hh ← Lean.Meta.mkAppM ``heq_of_eq #[eh]
            let cache' ← IO.mkRef ((← cache.get).insert (af, bf) hh)
            -- Compare the applications by transporting the head equality first.
            let ct ← Lean.Meta.mkHCongrWithArity af aa.size
            let mut args := #[]
            for k in [:aa.size] do
              let h ← coefficientInstanceHEq cache' aa[k]! ba[k]! fuel
              let h ← match ct.argKinds[k]! with
                | .eq => Lean.Meta.mkAppM ``eq_of_heq #[h]
                | .heq => pure h
                | _ => throwError "unexpected argument kind"
              args := args ++ #[aa[k]!, ba[k]!, h]
            -- hcongr works with a fixed head; transport the right head before applying it.
            let leftProof := Lean.mkAppN ct.proof args
            let headFn ← Lean.Meta.withLocalDeclD `head (← Lean.Meta.inferType af) fun z ↦
              Lean.Meta.mkLambdaFVars #[z] (Lean.mkAppN z ba)
            let transport ← Lean.Meta.mkAppM ``congrArg #[headFn, eh]
            let leftProof ← if (← Lean.Meta.inferType leftProof).isEq then
              Lean.Meta.mkAppM ``heq_of_eq #[leftProof] else pure leftProof
            let transport ← Lean.Meta.mkAppM ``heq_of_eq #[transport]
            return ← Lean.Meta.mkAppM ``HEq.trans #[leftProof, transport]
      let sameHead ← match af, bf with
        | .const n _, .const m _ =>
          if n == m then Lean.Meta.isDefEq af bf else pure false
        | _, _ => pure (af == bf)
      if sameHead && aa.size == ba.size && !aa.isEmpty then
        let ct ← Lean.Meta.mkHCongrWithArity af aa.size
        let mut args := #[]
        for i in [:aa.size] do
          let h ← try coefficientInstanceHEq cache aa[i]! ba[i]! fuel
            catch ex => throwError "{ex.toMessageData}\nIn argument {i} of {af}"
          let h ← match ct.argKinds[i]! with
            | .eq => Lean.Meta.mkAppM ``eq_of_heq #[h]
            | .heq => pure h
            | _ => throwError "unexpected congruence argument kind"
          args := args ++ #[aa[i]!, ba[i]!, h]
        let h := Lean.mkAppN ct.proof args
        let h ← if (← Lean.Meta.inferType h).isEq then
          Lean.Meta.mkAppM ``heq_of_eq #[h]
        else pure h
        return h
      throwError "cannot structurally compare\n{a}\nWITH\n{b}"
  let h ← compute ()
  let h ← Lean.instantiateMVars h
  let h ← if a == b then pure h else do
    let h ← Lean.Meta.mkAuxTheorem (← Lean.Meta.mkAppM ``HEq #[a, b]) h
      (zetaDelta := true) (kind? := `_chart_congr)
    pure h
  cache.modify (fun c ↦ c.insert (a, b) h)
  return h

end


set_option maxHeartbeats 400000 in
-- Explicit certificates avoid a large conversion between cached derived instances.
private theorem coefficientCFormula (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    (K : D Λ Z) (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    c Λ f g K =
      let J := (rightDerivedUpperShriek Λ (f ≫ g)).obj K
      let hJ := plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hK
      ((standingExceptionalHomEquiv Λ g (hJ.rightDerivedLowerShriek_obj f) hK).trans
        (standingExceptionalHomEquiv Λ f hJ (plus_rightDerivedUpperShriek_obj g hK)))
        ((originCompositionAmbient Λ f g).hom.app ⟨J, hJ⟩ ≫
          (standingExceptionalHomEquiv Λ (f ≫ g) hJ hK).symm (𝟙 J)) := by
  classical
  have hJ := plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hK
  dsimp only
  run_tac Lean.Elab.Tactic.withMainContext do
    let target ← Lean.Meta.whnf (← Lean.Elab.Tactic.getMainTarget)
    let some (_, lhs, rhs) := target.eq? | throwError "expected an equality: {target}"
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let h ← coefficientInstanceHEq cache lhs rhs 3000
    (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.mkAppM ``eq_of_heq #[h])


section Encoding
open FiniteDiscreteOrdinary CondensedBridge
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Finite A] [DiscreteTopology A]

omit [DiscreteTopology A] in
private theorem homNormalization (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]
    (M : Native A X) (K : Native A Y)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
      ((N A E X).obj M))
    (hK : _root_.DerivedCategory.TStructure.t.plus ((N A E Y).obj K))
    (b : (nativeSupport A f).obj M ⟶ K) :
    (N A E X).map (exceptionalHomEquiv A E f M K hM hK b) ≫
      (exceptionalComparison A E f K).hom =
    standingExceptionalHomEquiv (ULift.{u + 1} A) f hM hK
      ((canonicalSupport A E f).inv.app M ≫ (N A E Y).map b) := by
  let a := standingExceptionalHomEquiv (ULift.{u + 1} A) f hM hK
    ((canonicalSupport A E f).inv.app M ≫ (N A E Y).map b)
  change (E X).fixedDerived.functor.map
    (((E X).fixedDerived.toAdjunction.homEquiv M _) a) ≫
      (E X).fixedDerived.toAdjunction.counit.app _ = a
  exact ((E X).fixedDerived.toAdjunction.homEquiv M _).symm_apply_apply a


omit [DiscreteTopology A] in
private theorem counitNormalization (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [CompactSpace Y] (K : Native A Y)
    (hK : _root_.DerivedCategory.TStructure.t.plus ((N A E Y).obj K)) :
    (N A E Y).map (nativeEpsilon A E f K) =
      (canonicalSupport A E f).hom.app _ ≫
        (F (ULift.{u + 1} A) f).map (exceptionalComparison A E f K).hom ≫
        epsilon (ULift.{u + 1} A) f ((N A E Y).obj K) := by
  classical
  let j := exceptionalComparison A E f K
  have hG := plusEtaleOrigin_rightDerivedUpperShriek_obj f hK
  have hM := (DerivedCategory.plusEtaleOrigin
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).prop_of_iso j.symm hG
  have he := homNormalization A E f ((exceptional A E f).obj K) K hM hK
    (nativeEpsilon A E f K)
  have hid : exceptionalHomEquiv A E f _ K hM hK (nativeEpsilon A E f K) = 𝟙 _ := by
    simp only [nativeEpsilon, dif_pos hK, dif_pos hM, Equiv.apply_symm_apply]
  rw [hid] at he
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at he
  have hj := standingHom_left (ULift.{u + 1} A) f hM hG hK j.hom
    (epsilon (ULift.{u + 1} A) f ((N A E Y).obj K))
  simp only [epsilon, dif_pos hK, Equiv.apply_symm_apply, Category.comp_id] at hj
  have hh := (standingExceptionalHomEquiv (ULift.{u + 1} A) f hM hK).injective
    (he.symm.trans hj.symm)
  have hh' : (canonicalSupport A E f).inv.app _ ≫
      (N A E Y).map (nativeEpsilon A E f K) =
      (F (ULift.{u + 1} A) f).map j.hom ≫
        epsilon (ULift.{u + 1} A) f ((N A E Y).obj K) := by
    simpa only [epsilon, dif_pos hK] using hh
  calc
    _ = (canonicalSupport A E f).hom.app _ ≫
        ((canonicalSupport A E f).inv.app _ ≫
          (N A E Y).map (nativeEpsilon A E f K)) := by
      simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    _ = _ := congrArg (fun a ↦ (canonicalSupport A E f).hom.app _ ≫ a) hh'


set_option maxHeartbeats 1600000 in
-- The origin compositor has large cached coefficient instances.
omit [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] in
private theorem alpha_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    {M M' : D (ULift.{u + 1} A) X}
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X M)
    (hM' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X M')
    (j : M ⟶ M') :
    (F (ULift.{u + 1} A) g).map ((F (ULift.{u + 1} A) f).map j) ≫
        alpha (ULift.{u + 1} A) f g M' =
      alpha (ULift.{u + 1} A) f g M ≫ (F (ULift.{u + 1} A) (f ≫ g)).map j := by
  classical
  simp only [alpha, dif_pos hM, dif_pos hM']
  have hn := (originCompositionAmbient (ULift.{u + 1} A) f g).hom.naturality
    (ObjectProperty.homMk j :
      (⟨M, hM⟩ : (DerivedCategory.plusEtaleOrigin
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).FullSubcategory) ⟶ ⟨M', hM'⟩)
  dsimp only [Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map,
    ObjectProperty.ι_obj, ObjectProperty.homMk_hom] at hn
  dsimp only [D, F] at hn ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let name := Lean.mkIdent `hn
    let input ← Lean.Elab.Term.elabTerm (← `($name)) none
    let actual ← Lean.Meta.inferType input
    let expected ← Lean.Elab.Tactic.getMainTarget
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let h ← coefficientInstanceHEq cache actual expected 3000
    let h := Lean.mkAppN (Lean.mkConst ``eq_of_heq [.succ .zero])
      #[Lean.mkSort .zero, actual, expected, h]
    let proof := Lean.mkAppN (Lean.mkConst ``Eq.mp [.zero])
      #[actual, expected, h, input]
    (← Lean.Elab.Tactic.getMainGoal).assign proof

set_option maxHeartbeats 1600000 in
-- The explicit standing Hom transport traverses cached derived-category instances.
omit [DiscreteTopology A] in
/-- Conjugating the specified compact-support compositor and counit through two
standing exceptional Hom bijections gives the specified exceptional compositor.
Source: the finite coefficient paragraph of the composition proof, Step 2
(blueprint: lem-pur-composition-tensor-coefficient-adjunction).

Proof: the Hom normalization is the triangle identity of the coefficient equivalence.
Apply it to the inverse Hom image of the identity to obtain the counit normalization.
The compact-support encoding is natural. Expand the definition of nativeAlpha and
cancel its encoding isomorphisms. Its composite with the normalized native counit
becomes the ordinary alpha followed by epsilon, precomposed with the exceptional
comparison at the composite. The two Hom normalizations and naturality on the left
and right transfer this precomposition through the two standing Hom bijections.
The result is the exceptional comparison followed by c. The plus and etale-origin
guards hold because exceptional images have etale origins and compact support
preserves that class; coefficient isomorphisms preserve the same properties. -/
theorem compositionTensorCoefficientAdjunction (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace Y] [CompactSpace Z]
    (K : Native A Z)
    (hK : _root_.DerivedCategory.TStructure.t.plus ((N A E Z).obj K)) :
    (N A E X).map (nativeC A E f g K) ≫
        (exceptionalComparison A E f ((exceptional A E g).obj K)).hom ≫
        (G (ULift.{u + 1} A) f).map (exceptionalComparison A E g K).hom =
      (exceptionalComparison A E (f ≫ g) K).hom ≫
        c (ULift.{u + 1} A) f g ((N A E Z).obj K) := by
  classical
  let M := (exceptional A E (f ≫ g)).obj K
  let j := exceptionalComparison A E (f ≫ g) K
  have hJ := plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hK
  have hM := (DerivedCategory.plusEtaleOrigin
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).prop_of_iso j.symm hJ
  have hF : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y
      ((N A E Y).obj ((nativeSupport A f).obj M)) :=
    (DerivedCategory.plusEtaleOrigin
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).prop_of_iso
      ((canonicalSupport A E f).app M).symm (hM.rightDerivedLowerShriek_obj f)
  have hGG := plusEtaleOrigin_rightDerivedUpperShriek_obj g hK
  have hG := ((DerivedCategory.plusEtaleOrigin
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).prop_of_iso
      (exceptionalComparison A E g K).symm hGG).plus
  let b := nativeAlpha A E f g M ≫ nativeEpsilon A E (f ≫ g) K
  let a := exceptionalHomEquiv A E g _ K hF hK b
  have hc :
      (F (ULift.{u + 1} A) g).map ((canonicalSupport A E f).inv.app M) ≫
        (canonicalSupport A E g).inv.app ((nativeSupport A f).obj M) ≫
        (N A E Z).map b =
      (F (ULift.{u + 1} A) g).map ((F (ULift.{u + 1} A) f).map j.hom) ≫
        alpha (ULift.{u + 1} A) f g ((G (ULift.{u + 1} A) (f ≫ g)).obj
          ((N A E Z).obj K)) ≫
        epsilon (ULift.{u + 1} A) (f ≫ g) ((N A E Z).obj K) := by
    dsimp only [b]
    have hε := counitNormalization A E (f ≫ g) K hK
    have hα : (N A E Z).map (nativeAlpha A E f g M) =
        (canonicalSupport A E g).hom.app _ ≫
          (F (ULift.{u + 1} A) g).map ((canonicalSupport A E f).hom.app M) ≫
          alpha (ULift.{u + 1} A) f g ((N A E X).obj M) ≫
          (canonicalSupport A E (f ≫ g)).inv.app M :=
      (N A E Z).map_preimage _
    rw [(N A E Z).map_comp, hα, hε]
    simp only [Category.assoc,
      Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, M]
    simpa only [Category.assoc] using congrArg
      (fun q ↦ q ≫ epsilon (ULift.{u + 1} A) (f ≫ g) ((N A E Z).obj K))
      (alpha_naturality A f g hM hJ j.hom).symm
  have hg := homNormalization A E g ((nativeSupport A f).obj M) K hF hK b
  have hf := homNormalization A E f M ((exceptional A E g).obj K) hM hG a
  have hF' : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y
      ((N A E Y).obj ((nativeSupport A f).obj ((exceptional A E (f ≫ g)).obj K))) := hF
  simp only [nativeC, dif_pos hK, dif_pos hM, dif_pos hF', dif_pos hG,
    Equiv.trans_apply]
  change (N A E X).map (exceptionalHomEquiv A E f M _ hM hG a) ≫ _ ≫ _ = _
  erw [← Category.assoc, hf,
    ← standingHom_right (ULift.{u + 1} A) f hM hG (plus_rightDerivedUpperShriek_obj g hK)]
  erw [Category.assoc, hg]
  erw [← standingHom_left (ULift.{u + 1} A) g (hM.rightDerivedLowerShriek_obj f) hF hK]
  erw [hc]
  erw [standingHom_left (ULift.{u + 1} A) g
    (hM.rightDerivedLowerShriek_obj f) (hJ.rightDerivedLowerShriek_obj f) hK]
  erw [standingHom_left (ULift.{u + 1} A) f hM hJ
    (plus_rightDerivedUpperShriek_obj g hK)]
  simp only [c, dif_pos hK, Equiv.trans_apply]
  dsimp only [ULift.commRing, ULift.ring]

end Encoding

end AlgebraicGeometry.ProEtale.CompositionTensorMate
