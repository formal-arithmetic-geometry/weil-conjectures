/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import WeilConjectures.SmoothPurity.RationalWeilPurity.RationalWeilPurityNaturalityMate
import WeilConjectures.SmoothPurity.RationalWeilPurity.FrobeniusCompactCompletedFiniteNormalization
import WeilConjectures.SmoothPurity.Derived.DerivedCompleteFiniteReductionDetection
import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionShiftedHomFiniteAlgClosed

/-! # Ambient compact-support Frobenius normalization

This is the strict ambient comparison used to remove the constructible wrapper
from the compact-support Frobenius normalization.
(blueprint: lem-pur-frobenius-compact-integral-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
-- Kernel-checked structural congruence, adapted from FrobeniusSystemExchangeInverse.
-- Explicit congruence proofs avoid repeatedly reducing sheafification choices.
namespace WeilConjectures.FrobeniusExchange
private meta def toEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let type ← Lean.Meta.inferType h
  let some (α, a, _, b) := type.heq? | throwError "expected HEq"
  let level ← Lean.Meta.getLevel α
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq [level]) #[α, a, b, h]

-- Adapt the kernel-checked congruence method of HigherDirectImageTransitionCoreComposition.
-- Build congruence proofs before reducing the large derived-category objects.
private meta def congrProofs
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (pairs : Array (Lean.Expr × Lean.Expr × Lean.Expr)) :
    Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => do
    throwError "congruence depth exhausted: {a} versus {b}"
  | n + 1, a, b => do
    if let some h := (← cache.get).get? (a, b) then return h
    let compute : Lean.MetaM Lean.Expr := do
      let a := a.consumeMData
      let b := b.consumeMData
      if a == b then return ← Lean.Meta.mkHEqRefl a
      if a.isFVar then
        if let some value := (← Lean.Meta.getFVarLocalDecl a).value? then
          return ← congrProofs cache pairs n value b
      if b.isFVar then
        if let some value := (← Lean.Meta.getFVarLocalDecl b).value? then
          return ← congrProofs cache pairs n a value
      if a.getAppFn.isFVar && !a.isFVar then
        if let some value := (← Lean.Meta.getFVarLocalDecl a.getAppFn).value? then
          return ← congrProofs cache pairs n (Lean.mkAppN value a.getAppArgs).headBeta b
      if b.getAppFn.isFVar && !b.isFVar then
        if let some value := (← Lean.Meta.getFVarLocalDecl b.getAppFn).value? then
          return ← congrProofs cache pairs n a (Lean.mkAppN value b.getAppArgs).headBeta
      let normalize (e : Lean.Expr) : Lean.Expr :=
        match e.headBeta with
        | .letE _ _ value body _ => body.instantiate1 value
        | e' => e'
      let a' := normalize a
      let b' := normalize b
      if a != a' || b != b' then
        return ← congrProofs cache pairs n a' b'
      for (x, y, h) in pairs do
        if a == x && b == y then return h
        if a == y && b == x then return ← Lean.Meta.mkAppM ``HEq.symm #[h]
      if a == b then
        return ← Lean.Meta.mkHEqRefl a
      if a.isAppOfArity ``Eq.mpr 4 then
        let args := a.getAppArgs
        let hs ← Lean.Meta.mkAppM ``Eq.symm #[args[2]!]
        let hc ← Lean.Meta.mkAppM ``cast_heq #[hs, args[3]!]
        let ht ← congrProofs cache pairs n args[3]! b
        return ← Lean.Meta.mkAppM ``HEq.trans #[hc, ht]
      if b.isAppOfArity ``Eq.mpr 4 then
        let args := b.getAppArgs
        let hs ← Lean.Meta.mkAppM ``Eq.symm #[args[2]!]
        let hc ← Lean.Meta.mkAppM ``cast_heq #[hs, args[3]!]
        let ht ← congrProofs cache pairs n a args[3]!
        let hc ← Lean.Meta.mkAppM ``HEq.symm #[hc]
        return ← Lean.Meta.mkAppM ``HEq.trans #[ht, hc]
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let .lam name type body info := a then
        if let .lam name' type' body' info' := b then
          let htype ← congrProofs cache pairs n type type'
          let htype ← toEq htype
          return ← Lean.Meta.withLocalDecl name info type fun x =>
            Lean.Meta.withLocalDecl name' info' type' fun y => do
              let hxy ← Lean.Meta.mkHEq x y
              Lean.Meta.withLocalDeclD `hxy hxy fun hxy => do
                let h ← congrProofs cache (pairs.push (x, y, hxy)) n
                  (body.instantiate1 x) (body'.instantiate1 y)
                let h ← Lean.Meta.mkLambdaFVars #[x, y, hxy] h
                Lean.Meta.mkAppM ``Function.hfunext #[htype, h]
      let expandProjection (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let fn := e.getAppFn
        let .proj typeName index major := fn | return e
        let info := Lean.getStructureInfo (← Lean.getEnv) typeName
        let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
        return Lean.mkAppN p e.getAppArgs
      let a' ← expandProjection a
      let b' ← expandProjection b
      if a != a' || b != b' then
        return ← congrProofs cache pairs n a' b'
      let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let args := e.getAppArgs
        if e.isAppOf ``CategoryTheory.Functor.obj && args.size ==
            (← Lean.getConstInfo ``CategoryTheory.Functor.obj).type.getNumHeadForalls then
          let mut functor := args[args.size - 2]!
          for _ in [:20] do
            if functor.isFVar then
              if let some value := (← Lean.Meta.getFVarLocalDecl functor).value? then
                functor := value.headBeta
              else break
            else break
          for _ in [:8] do
            if functor.isAppOf ``directImageFunctor ||
                functor.isAppOf ``constructibleIntegralPullback ||
                functor.isAppOf ``integralDirectImage || functor.isAppOf ``realize ||
                functor.isAppOf ``coefficientSequenceLimit || functor.isAppOf ``compactImage then
              if let some value ← Lean.Meta.unfoldDefinition? functor
                  (ignoreTransparency := true) then
                functor := value.headBeta
              else break
            else break
          if functor.isAppOf ``ObjectProperty.ι then
            return ← Lean.Meta.mkAppM ``ObjectProperty.FullSubcategory.obj #[args.back!]
          if functor.isAppOf ``ObjectProperty.lift then
            let fs := functor.getAppArgs
            let obj ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs[fs.size - 2]!, args.back!]
            let prop := Lean.mkApp fs.back! args.back!
            return ← Lean.Meta.mkAppM ``ObjectProperty.FullSubcategory.mk #[obj, prop]
          let fs := functor.getAppArgs
          if functor.isAppOf ``CategoryTheory.Functor.obj && fs.size ==
              (← Lean.getConstInfo ``CategoryTheory.Functor.obj).type.getNumHeadForalls then
            if fs[fs.size - 2]!.isAppOf ``CategoryTheory.Functor.const then
              return fs.back!
          if functor.isAppOf ``CategoryTheory.Over.forget then
            return ← Lean.Meta.mkAppM ``CategoryTheory.Over.left #[args.back!]
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
              #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
        if e.isAppOf ``NatTrans.app && args.size ==
            (← Lean.getConstInfo ``NatTrans.app).type.getNumHeadForalls then
          let trans := args[args.size - 2]!
          let ts := trans.getAppArgs
          if trans.isAppOf ``whiskerLeft then
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[ts[ts.size - 4]!, args.back!]
            return ← Lean.Meta.mkAppM ``NatTrans.app #[ts.back!, x]
          if trans.isAppOf ``whiskerRight then
            let x ← Lean.Meta.mkAppM ``NatTrans.app #[ts[ts.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.map #[ts.back!, x]
        if e.isAppOf ``CategoryTheory.Functor.map && args.size ==
            (← Lean.getConstInfo ``CategoryTheory.Functor.map).type.getNumHeadForalls then
          let mut functor := args[args.size - 4]!
          for _ in [:8] do
            if functor.isAppOf ``coefficientSequenceLimit || functor.isAppOf ``realize then
              if let some value ← Lean.Meta.unfoldDefinition? functor
                  (ignoreTransparency := true) then
                functor := value.headBeta
              else break
            else break
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.map #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.map #[fs.back!, x]
        if e.isAppOf ``ObjectProperty.FullSubcategory.obj then
          let major := args.back!
          if major.isAppOf ``ObjectProperty.FullSubcategory.mk then
            let ms := major.getAppArgs
            return ms[ms.size - 2]!
        if e.isAppOf ``CategoryTheory.Limits.Cone.pt && args.size ==
            (← Lean.getConstInfo ``CategoryTheory.Limits.Cone.pt).type.getNumHeadForalls then
          let cone := args.back!
          if cone.isAppOf ``CategoryTheory.Limits.Cone.whisker ||
              cone.isAppOf ``CategoryTheory.Functor.mapCone then
            return ← Lean.Meta.withTransparency .default (Lean.Meta.whnf e)
        return e
      let a' ← expandCompositeObj a
      let b' ← expandCompositeObj b
      if a != a' || b != b' then
        return ← congrProofs cache pairs n a' b'
      let af := a.getAppFn
      let bf := b.getAppFn
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if af.isConstOf ``CategoryTheory.Preadditive.mk &&
          bf.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Preadditive.mk &&
          af.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if af.isConstOf ``CategoryTheory.Functor.mk &&
          bf.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Functor.mk &&
          af.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      let sameHead := af == bf || (af.isConst && bf.isConst &&
        af.constName! == bf.constName! && (← Lean.Meta.isDefEq af bf))
      if !sameHead || aa.size != ba.size then
        let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
          if f.isConst then
            return (← Lean.getProjectionFnInfo? f.constName!).isSome
          return false
        if !(← isProjection af) then
          if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
            return ← congrProofs cache pairs n a' b
        if !(← isProjection bf) then
          if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
            return ← congrProofs cache pairs n a b'
        let reduceProjection (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
          let some e' ← Lean.Meta.withTransparency .instances
              (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
          let some f ← Lean.Meta.withTransparency .all
              (Lean.Meta.reduceProj? e'.getAppFn) | return none
          let e'' := Lean.mkAppN f e'.getAppArgs
          if e'' == e then return none
          if e''.getAppFn.isProj then
            let .proj typeName index major := e''.getAppFn | return none
            let info := Lean.getStructureInfo (← Lean.getEnv) typeName
            let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
            let e''' := Lean.mkAppN p e''.getAppArgs
            if e''' == e then return none
          return some e''
        if ← isProjection af then
          if let some a' ← reduceProjection a then
            return ← congrProofs cache pairs n a' b
        if ← isProjection bf then
          if let some b' ← reduceProjection b then
            return ← congrProofs cache pairs n a b'
        if ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq a b) then
          return ← Lean.Meta.mkHEqRefl a
        throwError "different heads: {a} versus {b}"
      let mut first := 0
      while first < aa.size && aa[first]! == ba[first]! do
        first := first + 1
      let f := Lean.mkAppN af (aa.extract 0 first)
      let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
      let mut args := #[]
      for i in [first:aa.size] do
        let h ← congrProofs cache pairs n aa[i]! ba[i]!
        let h ← if ct.argKinds[i - first]! == .eq then
          toEq h else pure h
        args := args.push aa[i]! |>.push ba[i]! |>.push h
      return Lean.mkAppN ct.proof args
    let h ← compute
    cache.modify fun m => m.insert (a, b) h
    return h

private meta def structuralExact (proof : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let expected ← Lean.instantiateMVars (← goal.getType)
    let actual ← Lean.instantiateMVars (← Lean.Meta.inferType proof)
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    if let some (_, lhs, rhs) := expected.eq? then
      if let some (_, lhs', rhs') := actual.eq? then
        let hl ← Lean.Meta.withTransparency .reducible
          (congrProofs cache #[] 300 lhs lhs')
        let hr ← Lean.Meta.withTransparency .reducible
          (congrProofs cache #[] 300 rhs' rhs)
        let hm ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
        let hh ← Lean.Meta.mkAppM ``HEq.trans #[hl, hm]
        let hh ← Lean.Meta.mkAppM ``HEq.trans #[hh, hr]
        goal.assign (← toEq hh)
        return
    let heq ← Lean.Meta.withTransparency .reducible (congrProofs cache #[] 200 expected actual)
    let eq ← toEq heq
    goal.assign (← Lean.Meta.mkAppM ``Eq.mpr #[eq, proof])

-- Cast each categorical argument along an explicit equality of its type. This avoids
-- repeatedly reducing large sheafification instances during kernel checking.
private meta def repairApplication (proof : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let mut f := proof.getAppFn
  for arg in proof.getAppArgs do
    let type ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf (← Lean.Meta.inferType f))
    let .forallE _ expected _ _ := type | throwError "expected function type"
    let actual ← Lean.Meta.inferType arg
    let mut arg := arg
    if expected != actual then
      let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
      let h ← Lean.Meta.withTransparency .reducible (congrProofs cache #[] 300 expected actual)
      let h ← toEq h
      arg ← Lean.Meta.mkAppM ``Eq.mpr #[h, arg]
    f := Lean.mkApp f arg
  return f

end WeilConjectures.FrobeniusExchange

namespace WeilConjectures

attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard scalarReductionDerivedExistence
  completedIntegralCoefficientSheafUnrestricted FrobeniusExchange.models
  FrobeniusExchange.compactIntegral RationalWeilPurity.integralExchange
  FrobeniusExchange.compactFiniteCoordinates
  sfCompactSupportFiniteReductionIso scalarReductionDerivedExtension
attribute [local implicit_reducible] constructibleIntegralPullback
  RationalWeilPurity.integralFrobenius FiniteFieldDatum.geometricFiber zlFiberMap
  SheafOfModules.instAbelian abelianOfAdjunction Abelian.ofCoimageImageComparisonIsIso
  scalarReductionSourceDerived scalarReductionTargetDerived coefficientConstantTowerDerived
  integralOperationsCommHasDerivedCategory integralTowerHasDerivedCategory
  integralCompletedRingHasDerivedCategory

open Lean Elab Term in
local elab "ambient_repair% " h:term : term => do
  let p ← Lean.Elab.Term.elabTerm h none
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  FrobeniusExchange.repairApplication (← Lean.instantiateMVars p)

open Lean Elab Tactic in
local elab "ambient_structural_exact " n:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    FrobeniusExchange.structuralExact (← Lean.Meta.getLocalDeclFromUserName n.getId).toExpr

private theorem cancel_iso_hom {C : Type*} [Category C]
    {X Y Z : C} (i : Y ≅ Z) {a b : X ⟶ Y}
    (h : a ≫ i.hom = b ≫ i.hom) : a = b := by
  have h' := congrArg (fun t ↦ t ≫ i.inv) h
  simpa only [Category.assoc, i.hom_inv_id, Category.comp_id] using h'

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
/-- Compare one quotient in the recorded coordinates, then cancel the support isomorphism. -/
private theorem geometricReductionComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c₀ : Compactification f₀.left)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) (n : ℕ) :
    (scalarReductionDerivedExtension l E (D.geometricFiber Y₀).left n).map
        ((FrobeniusExchange.frobeniusCompactIntegral D l hl E f₀ c₀).app M).hom =
      (scalarReductionDerivedExtension l E (D.geometricFiber Y₀).left n).map
        (RationalWeilPurity.integralExchange D l hl f₀ E c₀ M).hom.hom := by
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).1
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).2
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let := (FrobeniusExchange.fiberMap_properties D f₀).1
  let := (FrobeniusExchange.fiberMap_properties D f₀).2.1
  let := (FrobeniusExchange.fiberMap_properties D f₀).2.2
  let : IsIso (D.geometricFrobenius X₀).hom := (D.geometricFrobenius X₀).isIso_hom
  let : IsIso (D.geometricFrobenius Y₀).hom := (D.geometricFrobenius Y₀).isIso_hom
  let c : Compactification (X := (D.geometricFiber X₀).left)
      (Y := (D.geometricFiber Y₀).left) (FrobeniusExchange.fiberMap D f₀) :=
    FrobeniusExchange.geometricCompactification D f₀ c₀
  let Q := (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom).obj M
  have hs := FrobeniusExchange.compactIntegral_finiteCoordinates
    (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left) l E D.k
    (zlClosurePrimeUnit D l hl) (FrobeniusExchange.fiberMap D f₀) c
    (D.geometricFrobenius X₀).hom
    (D.geometricFrobenius (zlCompactificationMiddle D f₀ c₀)).hom
    (D.geometricFrobenius Y₀).hom
    (D.frobenius_square_cartesian _ _ (zlCompactificationProper D f₀ c₀)).2.2.2.2.1
    (D.frobenius_square_cartesian _ _ (zlCompactificationOpen D f₀ c₀)).2.2.2.2.2.1 M n
  have hc := RationalWeilPurity.integralExchange_finiteCoordinates D l hl f₀ E c₀ M n
  have ht := ambient_repair% (hs.trans hc.symm)
  have hred := ambient_repair% (cancel_iso_hom (sfCompactSupportFiniteReductionIso l D.k
    (zlClosurePrimeUnit D l hl) c E Q n) ht)
  ambient_structural_exact hred

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
/-- Ambient compact-support normalization before the constructible wrapper.

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
`thm-pur-weil-equivariance-of-purity-and-trace.proof.md`, Step 2.

Proof: compare the normalized proper mate and inverse open mate on the whole
quotient system.  The quotient-unit formulas for the completion-to-ordinary
maps identify the two mate factors with the corresponding outer factors in
`RationalWeilPurity.integralExchange`.  The projection-normalized compact
realization identifies the middle realization and its inverse, so they cancel.
Pasting the three equalities gives the displayed ambient component equality;
the constructible inclusion is not used at this stage.  Empty schemes reduce
to the unique zero maps and identity compactifications to the mate triangle
identities.
(blueprint: lem-pur-frobenius-compact-integral-ambient-normalization).

Proof: apply the normalized proper/open mate calculation and projection-normalized
realization cancellation on the whole quotient system, then evaluate at `M`; no
finite-stage replacement is chosen. -/
theorem frobeniusCompactIntegral_ambient_normalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c₀ : Compactification f₀.left)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :
    HEq ((FrobeniusExchange.frobeniusCompactIntegral D l hl E f₀ c₀).app M).hom
      (RationalWeilPurity.integralExchange D l hl f₀ E c₀ M).hom.hom := by
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).1
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).2
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let := (FrobeniusExchange.fiberMap_properties D f₀).1
  let := (FrobeniusExchange.fiberMap_properties D f₀).2.1
  let := (FrobeniusExchange.fiberMap_properties D f₀).2.2
  let : IsIso (D.geometricFrobenius X₀).hom := (D.geometricFrobenius X₀).isIso_hom
  let : IsIso (D.geometricFrobenius Y₀).hom := (D.geometricFrobenius Y₀).isIso_hom
  let c : Compactification (X := (D.geometricFiber X₀).left)
      (Y := (D.geometricFiber Y₀).left) (FrobeniusExchange.fiberMap D f₀) :=
    FrobeniusExchange.geometricCompactification D f₀ c₀
  let F := sfCompactSupportFiniteIntegralFunctor l D.k (zlClosurePrimeUnit D l hl) c E
  let A := (F ⋙ constructibleIntegralPullback l E (D.geometricFrobenius Y₀).hom).obj M
  let B := (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom ⋙ F).obj M
  apply heq_of_eq
  apply derivedComplete_finiteReduction_ext l E (D.geometricFiber Y₀).left B.property.1
    (fun n ↦ integralReduction_shiftedHom_finite_algClosed l E D.k
      (zlClosurePrimeUnit D l hl) (D.geometricFiber Y₀).left A B n)
  intro n
  have h := geometricReductionComparison D l hl f₀ E c₀ M n
  ambient_structural_exact h

end WeilConjectures
