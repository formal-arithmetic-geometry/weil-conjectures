/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientNative
public import Sheaf.AlgebraicGeometry.RawModuleScalarClassMorphisms
public import Sheaf.AlgebraicGeometry.RawModuleScalarSourceFactors
import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackAbelianFormula


/-! # Concrete formulas for raw scalar comparison
Source: Stacks Project, Tags 03FD, 03Q8 and 03D7.
-/


@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale


private meta def scalarToEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let type ← Lean.Meta.inferType h
  let some (α, a, _, b) := type.heq? | throwError "expected HEq"
  let level ← Lean.Meta.getLevel α
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq [level]) #[α, a, b, h]

-- Keep assigned metavariables, local abbreviations and equivalent universe expressions
-- from triggering expansion of the large derived-category structures.
private meta def rawScalarCongrProofs
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (pairs : Array (Lean.Expr × Lean.Expr × Lean.Expr)) :
    Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => do
    throwError "congruence depth exhausted: {a} versus {b}"
  | n + 1, a, b => do
    let a ← Lean.instantiateMVars a
    let b ← Lean.instantiateMVars b
    if let some h := (← cache.get).get? (a, b) then return h
    let compute : Lean.MetaM Lean.Expr := do
      let a := a.consumeMData
      let b := b.consumeMData
      let normalize (e : Lean.Expr) : Lean.Expr :=
        match e.headBeta with
        | .letE _ _ value body _ => body.instantiate1 value
        | e' => e'
      let a' := normalize a
      let b' := normalize b
      if a != a' || b != b' then
        return ← rawScalarCongrProofs cache pairs n a' b'
      for (x, y, h) in pairs do
        if a == x && b == y then return h
        if a == y && b == x then return ← Lean.Meta.mkHEqSymm h
      if a == b then
        return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let .lam name type body info := a then
        if let .lam name' type' body' info' := b then
          let htype ← rawScalarCongrProofs cache pairs n type type'
          let htype ← scalarToEq htype
          return ← Lean.Meta.withLocalDecl name info type fun x =>
            Lean.Meta.withLocalDecl name' info' type' fun y => do
              let hxy ← Lean.Meta.mkHEq x y
              Lean.Meta.withLocalDeclD `hxy hxy fun hxy => do
                let h ← rawScalarCongrProofs cache (pairs.push (x, y, hxy)) n
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
        return ← rawScalarCongrProofs cache pairs n a' b'
      if let .fvar id := a then
        if let some value ← id.getValue? then
          return ← rawScalarCongrProofs cache pairs n value b
      if let .fvar id := b then
        if let some value ← id.getValue? then
          return ← rawScalarCongrProofs cache pairs n a value
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
      let sameHead ← if af == bf then pure true
        else if af.isConst && bf.isConst && af.constName! == bf.constName! then
          Lean.Meta.withTransparency .reducible (Lean.Meta.isDefEq af bf)
        else pure false
      if !sameHead || aa.size != ba.size then
        let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
          if f.isConst then
            return (← Lean.getProjectionFnInfo? f.constName!).isSome
          return false
        if !(← isProjection af) then
          if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
            return ← rawScalarCongrProofs cache pairs n a' b
        if !(← isProjection bf) then
          if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
            return ← rawScalarCongrProofs cache pairs n a b'
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
            return ← rawScalarCongrProofs cache pairs n a' b
        if ← isProjection bf then
          if let some b' ← reduceProjection b then
            return ← rawScalarCongrProofs cache pairs n a b'
        throwError "different congruence heads: {af} versus {bf}"
      let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let args := e.getAppArgs
        if e.isAppOf ``CategoryTheory.Functor.obj && args.size ≥ 2 then
          let functor := args[args.size - 2]!
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
              #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
        return e
      let a' ← expandCompositeObj a
      let b' ← expandCompositeObj b
      if a != a' || b != b' then
        return ← rawScalarCongrProofs cache pairs n a' b'
      let mut first := 0
      while first < aa.size && aa[first]! == ba[first]! do
        first := first + 1
      let f := Lean.mkAppN af (aa.extract 0 first)
      let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
      let mut args := #[]
      for i in [first:aa.size] do
        let h ← rawScalarCongrProofs cache pairs n aa[i]! ba[i]!
        let h ← if ct.argKinds[i - first]! == .eq then
          scalarToEq h else pure h
        args := args.push aa[i]! |>.push ba[i]! |>.push h
      return Lean.mkAppN ct.proof args
    let h ← compute
    cache.modify fun m => m.insert (a, b) h
    return h

set_option backward.isDefEq.respectTransparency true in
/-- Factorization of the two explicit raw pullbacks.
Source: Stacks Project, Tags 03FD and 03Q8, formula-expansion step of
lem-sbc-raw-module-abelian-hom-map-naturality.
(blueprint: lem-sbc-raw-scalar-pullback-formulas).

Proof: Evaluate higherDirectImageRawOverFunctor.map via
higherDirectImageRawOverPullbackHom_apply and expand higherDirectImageRawOverPullback and
higherDirectImageRawTrianglePullback. The first two factors are moduleSourceFactor and the last
two are moduleCoefficientFactor. Associativity joins the first two, leaving the derived image of
z in the middle. Expand abelianHigherDirectImageRawPullback on the arbitrary abelian class x.
Its first two factors are abelianSourceFactor and its last two are abelianCoefficientFactor, so
the same associativity equation gives the second identity. These are formulas for the two maps
separately; scalar comparison, its coherence and any relationship between z and x are not used.
All zero and identity cases follow from the same expansions. -/
theorem rawModuleScalar_pullback_formulas
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) (U : S.Etale)
    (A B : Over W) (f : A ⟶ B)
    (z : (higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).obj (op B)) :
    (rawModuleClassMorphism Λ k G (q : ℤ) U A
      ((higherDirectImageRawOverFunctor Λ k G (q : ℤ) U).map f.op z) =
      moduleSourceFactor Λ f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) ((freeSheaf Λ S).obj U) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.map
        (rawModuleClassMorphism Λ k G (q : ℤ) U B z) ≫
        moduleCoefficientFactorNative Λ G (q : ℤ) A B f) ∧
    (∀ (x : (abelianHigherDirectImageRawPresheaf (B.hom ≫ k) q
      (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B)).obj
        (op U)),
      rawAbelianClassMorphism (A.hom ≫ k)
        (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) A) q U
        (abelianHigherDirectImageRawPullback f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) q _ _
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app ((RawModuleScalarComparison.forget Λ W).obj G)) U x) =
      abelianSourceFactor f.left (B.hom ≫ k) (A.hom ≫ k)
        (Over.w_assoc f k) (RawModuleScalarComparison.freeAbelian S U) ≫
      (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.map
        (rawAbelianClassMorphism (B.hom ≫ k)
          (restrictedOverCoefficient ((RawModuleScalarComparison.forget Λ W).obj G) B) q U x) ≫
      abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G)
        (q : ℤ) A B f) := by
  constructor
  · run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let localExpr (name : Lean.Name) := do
          return (← Lean.Meta.getLocalDeclFromUserName name).toExpr
        let target ← Lean.instantiateMVars (← Lean.Meta.whnf (← goal.getType))
        let some (_, lhs, rhs) := target.consumeMData.eq?
          | throwError "expected equality"
        let ra := rhs.getAppArgs
        let source := ra[ra.size - 2]!
        let tail := ra.back!
        let some source ← Lean.Meta.unfoldDefinition? source (ignoreTransparency := true)
          | throwError "expected module source factor"
        let some source ← Lean.Meta.unfoldDefinition? source (ignoreTransparency := true)
          | throwError "expected triangle source factor"
        let sa := source.getAppArgs
        let proof ← Lean.Meta.mkAppM ``Category.assoc #[sa[sa.size - 2]!, sa.back!, tail]
        let proof ← Lean.Meta.mkAppM ``Eq.symm #[proof]
        let map := tail.getAppArgs[tail.getAppArgs.size - 2]!
        let native := map.getAppArgs.back!
        let hz ← Lean.Meta.mkAppM ``rawModuleClassMorphism_heq
          #[← localExpr `Λ, ← localExpr `k, ← localExpr `G,
            ← Lean.Meta.mkAppM ``Int.ofNat #[← localExpr `q],
            ← localExpr `U, ← localExpr `B, ← localExpr `z]
        let ht ← Lean.instantiateMVars (← Lean.Meta.whnf (← Lean.Meta.inferType hz))
        let some (_, _, _, raw) := ht.consumeMData.heq?
          | throwError "expected native class identity"
        let mut pairs := #[(native, raw, hz)]
        let hcoef ← Lean.Meta.mkAppM ``moduleCoefficientFactorNative_eq
          #[← localExpr `Λ, ← localExpr `G,
            ← Lean.Meta.mkAppM ``Int.ofNat #[← localExpr `q],
            ← localExpr `A, ← localExpr `B, ← localExpr `f]
        let some (_, coefficient, body) := (← Lean.Meta.inferType hcoef).eq?
          | throwError "expected coefficient computation rule"
        pairs := pairs.push (coefficient, body,
          ← Lean.Meta.mkAppM ``heq_of_eq #[hcoef])
        for name in [`A, `B] do
          let equation ← Lean.Meta.mkAppM ``higherDirectImageRawOverComplex_eq
            #[← localExpr `Λ, ← localExpr `G, ← localExpr name]
          let some (_, lhs, rhs) := (← Lean.Meta.inferType equation).eq?
            | throwError "expected complex equation"
          pairs := pairs.push (lhs, rhs, ← Lean.Meta.mkAppM ``heq_of_eq #[equation])
        let pt ← Lean.instantiateMVars (← Lean.Meta.whnf (← Lean.Meta.inferType proof))
        let some (_, lhs', rhs') := pt.consumeMData.eq?
          | throwError "expected factorization proof"
        let mapped := lhs.getAppArgs.back!
        let hread ← Lean.Meta.mkAppM ``rawModuleClassMorphism_heq
          #[← localExpr `Λ, ← localExpr `k, ← localExpr `G,
            ← Lean.Meta.mkAppM ``Int.ofNat #[← localExpr `q],
            ← localExpr `U, ← localExpr `A, mapped]
        let happly ← Lean.Meta.mkAppM ``higherDirectImageRawOverPullbackHom_apply
          #[← localExpr `Λ, ← localExpr `k, ← localExpr `G,
            ← Lean.Meta.mkAppM ``Int.ofNat #[← localExpr `q],
            ← localExpr `f, ← localExpr `U, ← localExpr `z]
        let some (_, _, rawPullback) := (← Lean.Meta.inferType happly).eq?
          | throwError "expected raw pullback evaluation"
        let hstart ← Lean.Meta.mkHEqTrans hread (← Lean.Meta.mkAppM ``heq_of_eq #[happly])
        let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
        let hl ← Lean.Meta.withTransparency .reducible
          (rawScalarCongrProofs cache pairs 200 rawPullback lhs')
        let hr ← Lean.Meta.withTransparency .reducible
          (rawScalarCongrProofs cache pairs 200 rhs' rhs)
        let hl ← Lean.Meta.mkHEqTrans hstart hl
        let hh ← Lean.Meta.mkHEqTrans hl (← Lean.Meta.mkAppM ``heq_of_eq #[proof])
        let hh ← Lean.Meta.mkHEqTrans hh hr
        goal.assign (← scalarToEq hh)
  · exact rawModuleScalar_pullback_abelian_formula Λ k G q U A B f

end AlgebraicGeometry.Etale
