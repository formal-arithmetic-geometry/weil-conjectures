/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.CategoryTheory.MateIsoAlongEquivalences

/-! # Whole-system Frobenius exchange inverses

Source: Deligne, Weil II (1.1.7), (1.1.10)--(1.1.11), (1.1.14), pp. 150--153;
agent-written whole-system argument in the DAG proof
(blueprint: lem-weil-frobenius-system-exchange-inverse).

The inverse is taken in the ordinary unbounded derived category of strict systems.
Evaluation is used to detect invertibility, never to detect equality of morphisms.
Integral realization uses the already specified alpha and beta comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

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

local elab "frobenius_structural_exact " n:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    structuralExact (← Lean.Meta.getLocalDeclFromUserName n.getId).toExpr

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

open Lean Elab Tactic in
local elab "frobenius_repair_exact " h:term : tactic => withMainContext do
  let p ← elabTerm h none
  structuralExact (← repairApplication p)

section IntegralIsoProof
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] models compactRealization

attribute [local implicit_reducible] SheafOfModules.instAbelian
  abelianOfAdjunction Abelian.ofCoimageImageComparisonIsIso
  scalarReductionSourceDerived scalarReductionTargetDerived
  coefficientConstantTowerDerived integralOperationsCommHasDerivedCategory
  integralTowerHasDerivedCategory integralCompletedRingHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
private theorem direct_integral_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (w : gX ≫ f = f ≫ gY) [IsIso (systemExchange l E f gX gY w)] :
    IsIso (directIntegral l E k hl f gX gY w) := by
  have : ∀ K : sfIntegralConstructibleCategory l E X,
      IsIso ((whiskerLeft (sfIntegralConstructible l E X).ι
        (sourceComparison l E (systemDirect l E f) gY)).app K) :=
    fun K ↦ directAlpha_isIso l E k hl f gY K
  have : IsIso (whiskerLeft (sfIntegralConstructible l E X).ι
      (sourceComparison l E (systemDirect l E f) gY)) := NatIso.isIso_of_isIso_app _
  have : IsIso (integralExchange l E (systemDirect l E f) gX gY
      (systemExchange l E f gX gY w)) := by
    unfold integralExchange
    infer_instance
  have : ∀ K : sfIntegralConstructibleCategory l E X,
      IsIso ((directIntegral l E k hl f gX gY w).app K) := by
    intro K
    apply (isIso_iff_of_reflects_iso _ (sfIntegralConstructible l E Y).ι).mp
    change IsIso ((integralExchange l E (systemDirect l E f) gX gY
      (systemExchange l E f gX gY w)).app K)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency.types true in
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
private theorem compact_integral_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (wp : gB ≫ c.g = c.g ≫ gY)
    (sj : IsPullback gX c.i c.i gB)
    [IsIso (systemCompactExchange l E c gX gB gY wp sj)] :
    IsIso (compactIntegral l E k hl f c gX gB gY wp sj) := by
  have : ∀ K : sfIntegralConstructibleCategory l E X,
      IsIso ((compactAlpha l E k hl f c gY).app K) :=
    fun K ↦ compactAlpha_isIso l E k hl f c gY K
  have : IsIso (compactAlpha l E k hl f c gY) := NatIso.isIso_of_isIso_app _
  have : IsIso (compactBeta l E k hl f c gX) := by
    unfold compactBeta
    infer_instance
  have : IsIso (compactIntegralAmbient l E k hl f c gX gB gY wp sj) := by
    unfold compactIntegralAmbient
    infer_instance
  have : ∀ K : sfIntegralConstructibleCategory l E X,
      IsIso ((compactIntegral l E k hl f c gX gB gY wp sj).app K) := by
    intro K
    apply (isIso_iff_of_reflects_iso _ (sfIntegralConstructible l E Y).ι).mp
    change IsIso ((compactIntegralAmbient l E k hl f c gX gB gY wp sj).app K)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end IntegralIsoProof

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)

/-- The actual whole-system direct mate for the geometric Frobenius square.
Source: Deligne (1.1.7)--(1.1.14); the square-exchange definition, item 1
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
abbrev frobeniusSystemDirect :=
  systemExchange l E (fiberMap D f₀) (galois D X₀) (galois D Y₀)
    (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1

/-- The actual proper/open whole-system composite with the retained compactification.
Source: Deligne (1.1.7)--(1.1.14); the square-exchange definition, item 2
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
abbrev frobeniusSystemCompact (c₀ : Compactification f₀.left) :=
  systemCompactExchange l E (geometricCompactification D f₀ c₀)
    (galois D X₀) (galois D (zlCompactificationMiddle D f₀ c₀)) (galois D Y₀)
    (D.frobenius_square_cartesian _ _ (zlCompactificationProper D f₀ c₀)).2.2.2.2.1
    (D.frobenius_square_cartesian _ _ (zlCompactificationOpen D f₀ c₀)).2.2.2.2.2.1

/-- The canonical direct-operation evaluation iso on an arbitrary strict system.
Source: the square-exchange definition and semilinear derived sections
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def systemDirectEvaluationIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  @asIso _ _ _ _ (systemDirectEvaluation l E f n) (systemDirectEvaluation_isIso l E f n)

/-- The canonical open-operation evaluation iso on an arbitrary strict system.
Source: the square-exchange definition and semilinear derived sections
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def systemOpenEvaluationIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  (@asIso _ _ _ _ (systemOpenEvaluationInv l E j n)
    (systemOpenEvaluationInv_isIso l E j n)).symm

/-- Evaluation of the full compact operation before any normalization or reduction.
Source: the square-exchange definition and semilinear derived sections
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def systemCompactEvaluationIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :=
  isoWhiskerLeft (systemDerivedOpen l E c.i) (systemDirectEvaluationIso l E c.g n) ≪≫
    isoWhiskerRight (systemOpenEvaluationIso l E c.i n)
      (proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l E (n + 1)))

/-- Source coordinates for finite evaluation of the direct Frobenius exchange.
Source: the specified operation and pullback comparisons of the square-exchange definition
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusDirectEvaluationSource (n : ℕ)
    (C : coefficientSequenceDerived l E (D.geometricFiber X₀).left) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (systemPullEvaluation l E (galois D Y₀) n).symm.app
      ((systemDirect l E (fiberMap D f₀)).obj C) ≪≫
    (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
      (galois D Y₀)).mapIso ((systemDirectEvaluationIso l E (fiberMap D f₀) n).app C) ≪≫
    (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
      (galois D Y₀)).symm.app
        ((proEtaleConstantDerivedDirectImage (fiberMap D f₀)
          (Padic.coefficientExtensionRing l E (n + 1))).obj
            ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C))

/-- Target coordinates for finite evaluation of the direct Frobenius exchange.
Source: the specified operation and pullback comparisons of the square-exchange definition
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusDirectEvaluationTarget (n : ℕ)
    (C : coefficientSequenceDerived l E (D.geometricFiber X₀).left) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (systemDirectEvaluationIso l E (fiberMap D f₀) n).app
      ((integralComparisonDerivedSequencePullback l E (galois D X₀)).obj C) ≪≫
    (proEtaleConstantDerivedDirectImage (fiberMap D f₀)
      (Padic.coefficientExtensionRing l E (n + 1))).mapIso
        ((systemPullEvaluation l E (galois D X₀) n).symm.app C ≪≫
          (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
            (galois D X₀)).symm.app
              ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C))

/-- Source coordinates for finite evaluation of the retained compact exchange.
Source: the specified proper/open operation comparisons of the square-exchange definition
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusCompactEvaluationSource (c₀ : Compactification f₀.left) (n : ℕ)
    (C : coefficientSequenceDerived l E (D.geometricFiber X₀).left) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (systemPullEvaluation l E (galois D Y₀) n).symm.app
      ((systemDerivedOpen l E (geometricCompactification D f₀ c₀).i ⋙
        systemDirect l E (geometricCompactification D f₀ c₀).g).obj C) ≪≫
    (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
      (galois D Y₀)).mapIso
        ((systemCompactEvaluationIso l E (geometricCompactification D f₀ c₀) n).app C) ≪≫
    (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
      (galois D Y₀)).symm.app
        ((sfIntrinsicCompactSupport (geometricCompactification D f₀ c₀)
          (Padic.coefficientExtensionRing l E (n + 1))).obj
            ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C))

/-- Target coordinates for finite evaluation of the retained compact exchange.
Source: the specified proper/open operation comparisons of the square-exchange definition
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusCompactEvaluationTarget (c₀ : Compactification f₀.left) (n : ℕ)
    (C : coefficientSequenceDerived l E (D.geometricFiber X₀).left) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  (systemCompactEvaluationIso l E (geometricCompactification D f₀ c₀) n).app
      ((integralComparisonDerivedSequencePullback l E (galois D X₀)).obj C) ≪≫
    (sfIntrinsicCompactSupport (geometricCompactification D f₀ c₀)
      (Padic.coefficientExtensionRing l E (n + 1))).mapIso
        ((systemPullEvaluation l E (galois D X₀) n).symm.app C ≪≫
          (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1))
            (galois D X₀)).symm.app
              ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C))

private theorem systemPull_equivalence {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (integralComparisonDerivedSequencePullback l E g).IsEquivalence := by
  let P := fun {V W : Scheme.{u}} (h : V ⟶ W) ↦
    integralComparisonDerivedSequencePullback l E h
  let a : P g ⋙ P (inv g) ≅ 𝟭 _ :=
    (integralComparisonSystemComposition l E (inv g) g).symm ≪≫
      eqToIso (congrArg (fun h : Y ⟶ Y ↦ P h) (IsIso.inv_hom_id g)) ≪≫
      integralComparisonSystemUnit l E Y
  let b : P (inv g) ⋙ P g ≅ 𝟭 _ :=
    (integralComparisonSystemComposition l E g (inv g)).symm ≪≫
      eqToIso (congrArg (fun h : X ⟶ X ↦ P h) (IsIso.hom_inv_id g)) ≪≫
      integralComparisonSystemUnit l E X
  exact Functor.IsEquivalence.mk' (P (inv g)) a.symm b

private theorem systemExchange_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (w : gX ≫ f = f ≫ gY) : IsIso (systemExchange l E f gX gY w) := by
  let := systemPull_equivalence l E gX
  let := systemPull_equivalence l E gY
  exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
    (systemAdjunction l E f) (systemAdjunction l E f)
    (integralComparisonDerivedSequencePullback l E gY)
    (integralComparisonDerivedSequencePullback l E gX) (systemSquare l E f gX gY w)

variable (hl : l ≠ D.p) [fs : IsSeparated f₀.left]
  [fft : LocallyOfFiniteType f₀.left] [fqc : QuasiCompact f₀.left]

set_option linter.unusedSectionVars false in
include hl fs fft fqc in
/-- The specified direct mate is an isomorphism on EVERY unbounded strict system.
Source: Deligne (1.1.7)--(1.1.14), pp. 150--153; agent-written DAG proof, steps 1--3
(blueprint: lem-weil-frobenius-system-exchange-inverse).
Proof: the canonical system pullback composition and identity isomorphisms
make pullback along geometric Frobenius an equivalence. Apply the mate-isomorphism
theorem to the actual system adjunction and its specified system square. The
result is invertibility of the existing whole-system natural transformation,
without evaluating it or imposing any bounds on its input. -/
theorem frobeniusSystemDirect_isIso : IsIso (frobeniusSystemDirect D l E f₀) := by
  let : IsIso (galois D X₀) := inferInstanceAs (IsIso (D.geometricFrobenius X₀).hom)
  let : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  exact systemExchange_isIso l E _ _ _ _

set_option linter.unusedSectionVars false in
include hl fs fft fqc in
/-- The retained compact-system exchange is an isomorphism on every unbounded system.
Source: Deligne (1.1.7)--(1.1.14), pp. 150--153; agent-written DAG proof, steps 1--3
(blueprint: lem-weil-frobenius-system-exchange-inverse).
Proof: pullback along geometric Frobenius on the compactification middle and
base is an equivalence, so the actual proper system mate is invertible by the
mate-isomorphism theorem. The existing open system exchange is already a natural
isomorphism. Whiskering and composition give invertibility of the compact exchange
on every unbounded system, using the retained compactification throughout. -/
theorem frobeniusSystemCompact_isIso (c₀ : Compactification f₀.left) :
    IsIso (frobeniusSystemCompact D l E f₀ c₀) := by
  let : IsIso (galois D (zlCompactificationMiddle D f₀ c₀)) :=
    inferInstanceAs (IsIso (D.geometricFrobenius (zlCompactificationMiddle D f₀ c₀)).hom)
  let : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  let := systemExchange_isIso l E (geometricCompactification D f₀ c₀).g
    (galois D (zlCompactificationMiddle D f₀ c₀)) (galois D Y₀)
    (D.frobenius_square_cartesian _ _ (zlCompactificationProper D f₀ c₀)).2.2.2.2.1
  unfold frobeniusSystemCompact systemCompactExchange
  infer_instance

/-- The uniquely determined inverse of the actual direct-system mate, as a natural iso.
Source: agent-written DAG proof, step 3, following Deligne (1.1.7)--(1.1.14)
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusSystemDirectIso :=
  @asIso _ _ _ _ (frobeniusSystemDirect D l E f₀)
    (frobeniusSystemDirect_isIso D l E f₀ hl)

/-- The uniquely determined inverse of the actual compact-system composite.
Source: agent-written DAG proof, step 3, following Deligne (1.1.7)--(1.1.14)
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusSystemCompactIso (c₀ : Compactification f₀.left) :=
  @asIso _ _ _ _ (frobeniusSystemCompact D l E f₀ c₀)
    (frobeniusSystemCompact_isIso D l E f₀ hl c₀)

section DirectEvaluationProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem evaluated_iso
    {V W : Type*} [Category V] [Category W] (F : V ⥤ W)
    {X Y : V} {A B : W} (i : X ≅ Y) (a : A ≅ F.obj X) (b : F.obj Y ≅ B)
    (t : A ⟶ B) (h : F.map i.hom ≫ b.hom = a.inv ≫ t) :
    ∃ I : A ≅ B, I.hom = t ∧ I.inv = b.inv ≫ F.map i.inv ≫ a.inv := by
  refine ⟨a ≪≫ F.mapIso i ≪≫ b, ?_, ?_⟩
  · apply (cancel_epi a.inv).1
    simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id_assoc] using h
  · simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc]

private theorem intrinsic_tensor_evaluated_iso
    {V W v w : Type*} [Category V] [Category W] [Category v] [Category w]
    (F : V ⥤ W) (GX : V ⥤ V) (GY : W ⥤ W) (f : v ⥤ w)
    (px qx : v ⥤ v) (py qy : w ⥤ w) (EX : V ⥤ v) (EY : W ⥤ w)
    (d₀ : F ⋙ EY ⟶ EX ⋙ f) [IsIso d₀] (pX : GX ⋙ EX ≅ EX ⋙ px) (pY : GY ⋙ EY ≅ EY ⋙ py)
    (bx : qx ≅ px) (bY : qy ≅ py) (i₀ : F ⋙ GY ⟶ GX ⋙ F) [IsIso i₀]
    (en : f ⋙ py ⟶ px ⋙ f)
    (C : V) (h : EY.map (i₀.app C) ≫ d₀.app (GX.obj C) ≫
        f.map (pX.hom.app C) = pY.hom.app (F.obj C) ≫
          py.map (d₀.app C) ≫ en.app (EX.obj C)) :
    let d := asIso d₀
    let i := asIso i₀
    let S := pY.app (F.obj C) ≪≫ py.mapIso (d.app C) ≪≫
      bY.symm.app (f.obj (EX.obj C))
    let T := d.app (GX.obj C) ≪≫ f.mapIso (pX.app C ≪≫ bx.symm.app (EX.obj C))
    ∃ I : qy.obj (f.obj (EX.obj C)) ≅ f.obj (qx.obj (EX.obj C)),
      I.hom = (whiskerLeft f bY.hom ≫ en ≫ whiskerRight bx.inv f).app (EX.obj C) ∧
        I.inv = T.inv ≫ EY.map (i.inv.app C) ≫ S.hom := by
  intro d i S T
  apply evaluated_iso EY (i.app C) S.symm T
  dsimp only [S, T]
  simp only [d, i, asIso_hom, Iso.symm_inv, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  simpa only [Category.assoc] using congrArg
    (fun t ↦ t ≫ f.map (bx.inv.app (EX.obj C))) h

attribute [local implicit_reducible] SheafOfModules.instAbelian
  abelianOfAdjunction Abelian.ofCoimageImageComparisonIsIso
  scalarReductionSourceDerived scalarReductionTargetDerived
  coefficientConstantTowerDerived integralOperationsCommHasDerivedCategory
  integralTowerHasDerivedCategory integralCompletedRingHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance] HasDerivedCategory.standard

attribute [local irreducible] finiteTensorExchange

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
private theorem system_inverse_evaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY) [IsIso (systemExchange l E f gX gY w)] (n : ℕ)
    (C : coefficientSequenceDerived l E X) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let d := @asIso _ _ _ _ (systemDirectEvaluation l E f n)
      (systemDirectEvaluation_isIso l E f n)
    let EX := coefficientSequenceDerivedEvaluation l E X n
    let EY := coefficientSequenceDerivedEvaluation l E Y n
    let pX := (systemPullEvaluation l E gX n).symm
    let pY := (systemPullEvaluation l E gY n).symm
    let bx := openSquareDerivedPullbackModel A gX
    let bY := openSquareDerivedPullbackModel A gY
    let S := pY.app ((systemDirect l E f).obj C) ≪≫
      (sfIntrinsicDerivedPullback A gY).mapIso (d.app C) ≪≫
      bY.symm.app ((proEtaleConstantDerivedDirectImage f A).obj (EX.obj C))
    let T := d.app ((integralComparisonDerivedSequencePullback l E gX).obj C) ≪≫
      (proEtaleConstantDerivedDirectImage f A).mapIso (pX.app C ≪≫ bx.symm.app (EX.obj C))
    ∃ I : (proEtaleConstantRingDerivedPullback A gY).obj
          ((proEtaleConstantDerivedDirectImage f A).obj (EX.obj C)) ≅
        (proEtaleConstantDerivedDirectImage f A).obj
          ((proEtaleConstantRingDerivedPullback A gX).obj (EX.obj C)),
      I.hom = (finiteTensorExchange A f f gX gY w).app (EX.obj C) ∧
      I.inv = T.inv ≫ EY.map ((asIso (systemExchange l E f gX gY w)).inv.app C) ≫
        S.hom := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  frobenius_repair_exact (@intrinsic_tensor_evaluated_iso
    (coefficientSequenceDerived l E X) (coefficientSequenceDerived l E Y)
    (normalizedDVRDerived l E X n) (normalizedDVRDerived l E Y n)
    inferInstance inferInstance inferInstance inferInstance
    (systemDirect l E f)
    (integralComparisonDerivedSequencePullback l E gX)
    (integralComparisonDerivedSequencePullback l E gY)
    (proEtaleConstantDerivedDirectImage f A)
    (sfIntrinsicDerivedPullback A gX)
    (proEtaleConstantRingDerivedPullback A gX)
    (sfIntrinsicDerivedPullback A gY)
    (proEtaleConstantRingDerivedPullback A gY)
    (coefficientSequenceDerivedEvaluation l E X n)
    (coefficientSequenceDerivedEvaluation l E Y n)
    (systemDirectEvaluation l E f n)
    (systemDirectEvaluation_isIso l E f n)
    (systemPullEvaluation l E gX n).symm
    (systemPullEvaluation l E gY n).symm
    (openSquareDerivedPullbackModel A gX)
    (openSquareDerivedPullbackModel A gY)
    (systemExchange l E f gX gY
      w)
    (inferInstance : IsIso (systemExchange l E f gX gY w))
    (finiteExchange A f f
      gX gY
      w)
    C
    (by
      have h := systemExchange_evaluation l E f gX gY w n C
      frobenius_structural_exact h))

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
/-- Finite evaluation of the actual inverse direct-system arrow is the inverse of
the specified finite direct exchange, through exactly the operation comparisons.
Source: Deligne (1.1.7)--(1.1.14); agent-written DAG proof, steps 1--3
(blueprint: lem-weil-frobenius-system-exchange-inverse).
Proof: evaluation compatibility identifies the forward system mate with the
specified finite direct mate. Apply evaluation to both inverse identities and
conjugate by the given source and target comparisons. Uniqueness of the inverse
gives the displayed finite iso and its inverse formula. No faithfulness is used. -/
theorem frobeniusSystemDirect_inverse_evaluation (n : ℕ)
    (C : coefficientSequenceDerived l E (D.geometricFiber X₀).left) :
    ∃ I : (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) (galois D Y₀)).obj
        ((proEtaleConstantDerivedDirectImage (fiberMap D f₀)
          (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C)) ≅
        (proEtaleConstantDerivedDirectImage (fiberMap D f₀)
          (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) (galois D X₀)).obj
          ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C)),
      I.hom = (frobeniusDirectFinite D l E (n + 1) (Nat.succ_pos n) f₀).app
        ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C) ∧
      I.inv = (frobeniusDirectEvaluationTarget D l E f₀ n C).inv ≫
        (coefficientSequenceDerivedEvaluation l E (D.geometricFiber Y₀).left n).map
          ((frobeniusSystemDirectIso D l E f₀ hl).inv.app C) ≫
        (frobeniusDirectEvaluationSource D l E f₀ n C).hom := by
  let := frobeniusSystemDirect_isIso D l E f₀ hl
  have h := system_inverse_evaluation l E (fiberMap D f₀) (galois D X₀) (galois D Y₀)
    (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1 n C
  frobenius_structural_exact h

end DirectEvaluationProof

/-- Finite evaluation of the inverse compact-system arrow is the inverse of the
specified chosen finite compact exchange on every unbounded system input.
Source: Deligne (1.1.7)--(1.1.14); agent-written DAG proof, steps 1--3
(blueprint: lem-weil-frobenius-system-exchange-inverse).
Proof: evaluate the actual proper/open composite using the normalized adjunction
and operation comparisons. It is the specified finite compact exchange with the
same retained model. Evaluate both whole-system inverse identities and conjugate
by these very source and target comparisons. Uniqueness gives the inverse formula. -/
theorem frobeniusSystemCompact_inverse_evaluation (c₀ : Compactification f₀.left)
    (n : ℕ) (C : coefficientSequenceDerived l E (D.geometricFiber X₀).left) :
    ∃ I : (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) (galois D Y₀)).obj
        ((sfIntrinsicCompactSupport (geometricCompactification D f₀ c₀)
          (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C)) ≅
        (sfIntrinsicCompactSupport (geometricCompactification D f₀ c₀)
          (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) (galois D X₀)).obj
          ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C)),
      I.hom = (frobeniusCompactFinite D f₀ c₀ l E (n + 1) (Nat.succ_pos n)).app
        ((coefficientSequenceDerivedEvaluation l E (D.geometricFiber X₀).left n).obj C) ∧
      I.inv = (frobeniusCompactEvaluationTarget D l E f₀ c₀ n C).inv ≫
        (coefficientSequenceDerivedEvaluation l E (D.geometricFiber Y₀).left n).map
          ((frobeniusSystemCompactIso D l E f₀ hl c₀).inv.app C) ≫
        (frobeniusCompactEvaluationSource D l E f₀ c₀ n C).hom := by
  sorry

include fs fft fqc in
attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
/-- The specified integral direct exchange is invertible on its full stated domain.
Source: Deligne (1.1.7)--(1.1.14); agent-written DAG proof, step 4
(blueprint: lem-weil-frobenius-system-exchange-inverse).
Proof: the total derived-limit functor of prop-weil-pbc-rlim-functoriality after
exact scalar restriction carries the two system inverse identities to inverse
identities. The specified alpha and beta comparisons are isomorphisms. Compose
their inverses with the realized system inverse. Associativity cancels alpha,
beta and the two middle factors, in either order. Naturality follows throughout. -/
theorem frobeniusDirectIntegral_isIso :
    IsIso (frobeniusDirectIntegral D l hl E f₀) := by
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let : IsIso (galois D X₀) := inferInstanceAs (IsIso (D.geometricFrobenius X₀).hom)
  let : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  let := frobeniusSystemDirect_isIso D l E f₀ hl
  exact direct_integral_iso (X := (D.geometricFiber X₀).left)
    (Y := (D.geometricFiber Y₀).left) l E D.k (zlClosurePrimeUnit D l hl) (fiberMap D f₀)
    (galois D X₀) (galois D Y₀) (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
/-- The specified integral compact exchange is invertible with the fixed model.
Source: Deligne (1.1.7)--(1.1.14); agent-written DAG proof, step 4
(blueprint: lem-weil-frobenius-system-exchange-inverse).
Proof: apply the total derived-limit functor, after exact scalar restriction, to
the two inverse identities of frobeniusSystemCompactIso on the reduction system.
Compose with the inverse of compactAlpha and compactBeta. The two comparison
inverse identities and the functorial inverse identities cancel in both orders.
The retained compactification is identical in the system and integral composites. -/
theorem frobeniusCompactIntegral_isIso (c₀ : Compactification f₀.left) :
    IsIso (frobeniusCompactIntegral D l hl E f₀ c₀) := by
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  let := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  let : IsIso (galois D X₀) := inferInstanceAs (IsIso (D.geometricFrobenius X₀).hom)
  let : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  let := (fiberMap_properties D f₀).1
  let := (fiberMap_properties D f₀).2.1
  let := (fiberMap_properties D f₀).2.2
  let := frobeniusSystemCompact_isIso D l E f₀ hl c₀
  exact compact_integral_iso (X := (D.geometricFiber X₀).left)
    (Y := (D.geometricFiber Y₀).left) l E D.k (zlClosurePrimeUnit D l hl)
    (fiberMap D f₀) (geometricCompactification D f₀ c₀)
    (galois D X₀) (galois D (zlCompactificationMiddle D f₀ c₀)) (galois D Y₀)
    (D.frobenius_square_cartesian _ _ (zlCompactificationProper D f₀ c₀)).2.2.2.2.1
    (D.frobenius_square_cartesian _ _ (zlCompactificationOpen D f₀ c₀)).2.2.2.2.2.1

/-- The integral direct exchange with its uniquely determined natural inverse.
Source: agent-written DAG proof, step 4, following Deligne (1.1.7)--(1.1.14)
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusDirectIntegralIso :=
  @asIso _ _ _ _ (frobeniusDirectIntegral D l hl E f₀)
    (frobeniusDirectIntegral_isIso D l E f₀ hl)

/-- The integral compact exchange with its uniquely determined natural inverse.
Source: agent-written DAG proof, step 4, following Deligne (1.1.7)--(1.1.14)
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusCompactIntegralIso (c₀ : Compactification f₀.left) :=
  @asIso _ _ _ _ (frobeniusCompactIntegral D l hl E f₀ c₀)
    (frobeniusCompactIntegral_isIso D l E f₀ hl c₀)

/-- Alpha-star, with the original sourceComparison as its forward map.
Source: the square-exchange definition, integral direct paragraph; DAG step 4
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusDirectAlphaIso
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  @asIso _ _ _ _
    ((sourceComparison l E (systemDirect l E (fiberMap D f₀)) (galois D Y₀)).app K.obj)
    (directAlpha_isIso (X := (D.geometricFiber X₀).left)
      (Y := (D.geometricFiber Y₀).left) l E D.k (zlClosurePrimeUnit D l hl) (fiberMap D f₀)
      (galois D Y₀) K)

/-- Beta-star is the same effective pullback counit inverse under the system operation.
Source: the square-exchange definition, integral direct paragraph; DAG step 4
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusDirectBetaIso :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  isoWhiskerRight (reductionPullbackIso l E (galois D X₀)).symm
    (systemDirect l E (fiberMap D f₀) ⋙ coefficientSequenceLimit l E (D.geometricFiber Y₀).left)

/-- Alpha-shriek with exactly the original compactAlpha as its forward map.
Source: the square-exchange definition, integral compact paragraph; DAG step 4
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusCompactAlphaIso (c₀ : Compactification f₀.left)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI := (fiberMap_properties D f₀).1
  letI := (fiberMap_properties D f₀).2.1
  letI := (fiberMap_properties D f₀).2.2
  @asIso _ _ _ _
    ((compactAlpha (X := (D.geometricFiber X₀).left)
      (Y := (D.geometricFiber Y₀).left) l E D.k (zlClosurePrimeUnit D l hl) (fiberMap D f₀)
      (geometricCompactification D f₀ c₀) (galois D Y₀)).app K)
    (compactAlpha_isIso (X := (D.geometricFiber X₀).left)
      (Y := (D.geometricFiber Y₀).left) l E D.k (zlClosurePrimeUnit D l hl) (fiberMap D f₀)
      (geometricCompactification D f₀ c₀) (galois D Y₀) K)

/-- Beta-shriek, using precisely the same projection-normalized compact realization.
Source: the square-exchange definition, integral compact paragraph; DAG step 4
(blueprint: lem-weil-frobenius-system-exchange-inverse). -/
def frobeniusCompactBetaIso (c₀ : Compactification f₀.left) :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI := (fiberMap_properties D f₀).1
  letI := (fiberMap_properties D f₀).2.1
  letI := (fiberMap_properties D f₀).2.2
  isoWhiskerRight (reductionPullbackIso l E (galois D X₀)).symm
      ((systemDerivedOpen l E (geometricCompactification D f₀ c₀).i ⋙
        systemDirect l E (geometricCompactification D f₀ c₀).g) ⋙
          coefficientSequenceLimit l E (D.geometricFiber Y₀).left) ≪≫
    isoWhiskerLeft (constructibleIntegralPullback l E (galois D X₀))
      (compactRealization (X := (D.geometricFiber X₀).left)
        (Y := (D.geometricFiber Y₀).left) l E D.k (zlClosurePrimeUnit D l hl)
        (fiberMap D f₀)
        (geometricCompactification D f₀ c₀)).symm

/-- The inverse of the specified integral direct exchange is alpha-inverse after
realization of the actual system inverse after beta-inverse (categorical order below).
Source: Deligne (1.1.7)--(1.1.14); agent-written DAG proof, step 4
(blueprint: lem-weil-frobenius-system-exchange-inverse).
Proof: unfold the integral exchange as alpha, L(e), beta. Functoriality of
Rlim after exact scalar restriction sends both inverse equations for e to inverse
equations for L(e). The two alpha and beta inverse equations then cancel adjacent
factors in both orders. Uniqueness of inverse gives this literal formula. -/
theorem frobeniusDirectIntegral_inverse
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :
    ((frobeniusDirectIntegralIso D l E f₀ hl).inv.app K).hom =
      (frobeniusDirectBetaIso D l E f₀ hl).inv.app K ≫
        (coefficientSequenceLimit l E (D.geometricFiber Y₀).left).map
          ((frobeniusSystemDirectIso D l E f₀ hl).inv.app
            ((reduction l E (D.geometricFiber X₀).left).obj K.obj)) ≫
        (frobeniusDirectAlphaIso D l E f₀ hl K).inv := by
  sorry

/-- The compact integral inverse is the reverse composite of the same three factors,
with the same fixed compactification in alpha, the whole-system inverse, and beta.
Source: Deligne (1.1.7)--(1.1.14); agent-written DAG proof, step 4
(blueprint: lem-weil-frobenius-system-exchange-inverse).
Proof: expand compactIntegralAmbient as compactAlpha, L(e-c), compactBeta.
Apply the total strict-tower derived-limit functor to the two inverse equations
for e-c on the simultaneous reduction system. Compose with the specified inverse
comparisons. Associativity cancels adjacent inverse pairs in both products;
uniqueness identifies this arrow with the integral inverse. -/
theorem frobeniusCompactIntegral_inverse (c₀ : Compactification f₀.left)
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :
    ((frobeniusCompactIntegralIso D l E f₀ hl c₀).inv.app K).hom =
      (frobeniusCompactBetaIso D l E f₀ hl c₀).inv.app K ≫
        (coefficientSequenceLimit l E (D.geometricFiber Y₀).left).map
          ((frobeniusSystemCompactIso D l E f₀ hl c₀).inv.app
            ((reduction l E (D.geometricFiber X₀).left).obj K.obj)) ≫
        (frobeniusCompactAlphaIso D l E f₀ hl c₀ K).inv := by
  sorry

end WeilConjectures.FrobeniusExchange
