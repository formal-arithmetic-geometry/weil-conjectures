/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.CompactSupportStrictScalarMate
public import Sheaf.Paper.CompactSupportScalarLimitReduction
public import Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps
import WeilConjectures.Compactification.Cofiltered
import Sheaf.Paper.RefinementExchangeCoherence
import Sheaf.Paper.ScalarRefinementOriginsE
import Sheaf.Paper.ScalarRefinementOriginsF
import Sheaf.Paper.StrictRefinementRestrictionSquares
import Sheaf.Paper.StrictScalarOpenUnit
import Sheaf.Paper.StrictScalarPullComposition
import Sheaf.Paper.StrictScalarOpenComposition
import Sheaf.Paper.StrictScalarProperComposition
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.CompactSupportReductionTower
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus

/-! # Strict scalar mates and compactification refinements

Source: Stacks, more-etale.tex, Tags 0F7B, 0F7C and 0F7D; the agent auxiliary
comparison, Steps 1--11 (blueprint: lem-pur-compact-support-strict-scalar-refinement).

All equations are in ordinary derived categories of strict module towers. Positive
index n+1 is encoded by n : ℕ. The maps use the existing clopen projection, proper
adjunction mate, native support-model comparison, scalar mate and total-limit maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective WeilConjectures.SemilinearSections.hasDerived
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] T U scalarAdj properRestriction openRestriction
  pastedRestriction comparison
attribute [local irreducible] AlgebraicGeometry.ProEtale.StrictTower.J
  AlgebraicGeometry.ProEtale.StrictTower.R AlgebraicGeometry.ProEtale.StrictTower.G

-- Structural congruence avoids expanding derived functors when their instance
-- proofs or functor-composition presentations differ. This is the kernel-checked
-- method of SmoothTensorCompositionEquation, restricted here to type transport.
private meta def instanceCongrToEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let type ← Lean.Meta.inferType h
  let some (α, a, _, b) := type.heq? | throwError "expected HEq"
  let level ← Lean.Meta.getLevel α
  return Lean.mkAppN (Lean.mkConst ``eq_of_heq [level]) #[α, a, b, h]

-- The congruence method of HigherDirectImageRawTransitionToHomCore, which also reads through
-- `let`s and `(𝟭 _).obj`. Build congruence proofs before reducing the large derived-category
-- objects, so that the kernel only meets proof irrelevance at the leaves.
private meta def instanceCongrHEq
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
      if a.isFVar then
        if let some v ← a.fvarId!.getValue? then
          return ← instanceCongrHEq cache pairs n v b
      if b.isFVar then
        if let some v ← b.fvarId!.getValue? then
          return ← instanceCongrHEq cache pairs n a v
      let normalize (e : Lean.Expr) : Lean.Expr :=
        match e.headBeta with
        | .letE _ _ value body _ => body.instantiate1 value
        | e' =>
          if (e'.isAppOfArity ``CategoryTheory.Functor.obj 6 ||
              e'.isAppOfArity ``CategoryTheory.Functor.map 8) &&
              (e'.getArg! 4).isAppOfArity ``CategoryTheory.Functor.id 2 then
            e'.getAppArgs.back!
          else e'
      let a' := normalize a
      let b' := normalize b
      if a != a' || b != b' then
        return ← instanceCongrHEq cache pairs n a' b'
      for (x, y, h) in pairs do
        if a == x && b == y then return h
        if a == y && b == x then return ← Lean.Meta.mkAppM ``HEq.symm #[h]
      if a == b then
        return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let .lam name type body info := a then
        if let .lam name' type' body' info' := b then
          let htype ← instanceCongrHEq cache pairs n type type'
          let htype ← instanceCongrToEq htype
          return ← Lean.Meta.withLocalDecl name info type fun x =>
            Lean.Meta.withLocalDecl name' info' type' fun y => do
              let hxy ← Lean.Meta.mkHEq x y
              Lean.Meta.withLocalDeclD `hxy hxy fun hxy => do
                let h ← instanceCongrHEq cache (pairs.push (x, y, hxy)) n
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
        return ← instanceCongrHEq cache pairs n a' b'
      let af := a.getAppFn.consumeMData
      let bf := b.getAppFn.consumeMData
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
      let sameHead ← if af == bf then pure true else
        if af.isConst && bf.isConst && af.constName! == bf.constName! then
          Lean.Meta.isDefEq af bf
        else pure false
      if sameHead && aa.size ≥ 4 && ba.size ≥ 4 &&
          (af.isConstOf ``CategoryTheory.Functor.obj ||
            af.isConstOf ``CategoryTheory.Functor.map ||
            af.isConstOf ``CategoryTheory.NatTrans.app) then
        let sameDomain ← Lean.Meta.isDefEq aa[0]! ba[0]!
        let sameCodomain ← Lean.Meta.isDefEq aa[2]! ba[2]!
        if !sameDomain || !sameCodomain then
          let reduceComponent (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
            let some e' ← Lean.Meta.withTransparency .instances
                (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
            let some f ← Lean.Meta.withTransparency .all
                (Lean.Meta.reduceProj? e'.getAppFn) | return none
            let e'' := Lean.mkAppN f e'.getAppArgs
            if e'' == e then return none
            return some e''
          if let some a' ← reduceComponent a then
            return ← instanceCongrHEq cache pairs n a' b
          if let some b' ← reduceComponent b then
            return ← instanceCongrHEq cache pairs n a b'
      if !sameHead || aa.size != ba.size then
        if ← Lean.Meta.withTransparency .reducible (Lean.Meta.isDefEq a b) then
          return ← Lean.Meta.mkHEqRefl a
        let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
          if f.isConst then
            return (← Lean.getProjectionFnInfo? f.constName!).isSome
          return false
        if !(← isProjection af) then
          if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
            return ← instanceCongrHEq cache pairs n a' b
        if !(← isProjection bf) then
          if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
            return ← instanceCongrHEq cache pairs n a b'
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
            return ← instanceCongrHEq cache pairs n a' b
        if ← isProjection bf then
          if let some b' ← reduceProjection b then
            return ← instanceCongrHEq cache pairs n a b'
        if ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq a b) then
          return ← Lean.Meta.mkHEqRefl a
        throwError "different congruence heads: {a} versus {b}"
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
        return ← instanceCongrHEq cache pairs n a' b'
      let build : Lean.MetaM Lean.Expr := do
        let mut first := 0
        while first < aa.size && aa[first]! == ba[first]! do
          first := first + 1
        let f := Lean.mkAppN af (aa.extract 0 first)
        let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
        let mut args := #[]
        for i in [first:aa.size] do
          let h ← instanceCongrHEq cache pairs n aa[i]! ba[i]!
          let h ← if ct.argKinds[i - first]! == .eq then
            instanceCongrToEq h else pure h
          args := args.push aa[i]! |>.push ba[i]! |>.push h
        return Lean.mkAppN ct.proof args
      try build catch err =>
        -- Equal applications can expose their functor parameters differently.
        -- Reduce a component projection before trying to compare those parameters.
        let reduceComponent (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
          let some e' ← Lean.Meta.withTransparency .instances
              (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
          let some f ← Lean.Meta.withTransparency .all
              (Lean.Meta.reduceProj? e'.getAppFn) | return none
          let e'' := Lean.mkAppN f e'.getAppArgs
          if e'' == e then return none
          return some e''
        if let some a' ← reduceComponent a then
          return ← instanceCongrHEq cache pairs n a' b
        if let some b' ← reduceComponent b then
          return ← instanceCongrHEq cache pairs n a b'
        throw err
    let h ← compute
    cache.modify fun m => m.insert (a, b) h
    return h


private meta def castProofArguments (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
  let mut out := e.getAppFn
  let mut type ← Lean.Meta.inferType out
  for arg in e.getAppArgs do
    type ← Lean.Meta.whnf type
    let .forallE _ dom body _ := type | throwError "expected function"
    let argType ← Lean.instantiateMVars (← Lean.Meta.inferType arg)
    let dom ← Lean.instantiateMVars dom
    let mut arg := arg
    if (← Lean.Meta.isProp dom) && argType != dom then
      let h ← instanceCongrHEq cache #[] 200 argType dom
      let h ← Lean.Meta.mkAppM ``eq_of_heq #[h]
      arg ← Lean.Meta.mkAppM ``Eq.mp #[h, arg]
    out := Lean.mkApp out arg
    type := body.instantiate1 arg
  return out

open Lean Elab Tactic Meta in
local elab "have_cast_args " name:ident " := " h:term : tactic => withMainContext do
  let proof ← instantiateMVars (← elabTerm h none)
  let proof ← castProofArguments proof
  let goal ← getMainGoal
  let (_, goal') ← goal.note name.getId proof
  replaceMainGoal [goal']

open Lean Elab Tactic Meta in
local elab "exact_congr_type " h:term : tactic => withMainContext do
  let proof ← elabTerm h none
  let target ← instantiateMVars (← getMainTarget)
  let proofType ← instantiateMVars (← inferType proof)
  let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
  let he ← instanceCongrHEq cache #[] 200 proofType target
  let e ← mkAppM ``eq_of_heq #[he]
  (← getMainGoal).assign (← mkAppM ``Eq.mp #[e, proof])

private theorem comparison_eq (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) :
    let : QuasiCompact c.i := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
    let : QuasiCompact d.i := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
    refinementComparison B r = compositionC B r := by
  rfl

attribute [local irreducible] compositionC

private theorem conjugate_app_isIso {C D : Type*} [Category C] [Category D]
    {F G H I : C ⥤ D} (e : F ≅ G) (a : G ⟶ H) (g : I ≅ H)
    (b : F ⟶ I) (hb : b = e.hom ≫ a ≫ g.inv)
    (M : C) (ha : IsIso (a.app M)) : IsIso (b.app M) := by
  subst b
  let := ha
  dsimp only [NatTrans.comp_app]
  infer_instance

private theorem scalar_cube_mates
    {VA WA SA ZA VB WB SB ZB : Type*}
    [Category VA] [Category WA] [Category SA] [Category ZA]
    [Category VB] [Category WB] [Category SB] [Category ZB]
    {gpA : ZA ⥤ WA} {rpA : WA ⥤ ZA} {grA : SA ⥤ VA} {rrA : VA ⥤ SA}
    {gpB : ZB ⥤ WB} {rpB : WB ⥤ ZB} {grB : SB ⥤ VB} {rrB : VB ⥤ SB}
    (apA : gpA ⊣ rpA) (arA : grA ⊣ rrA) (apB : gpB ⊣ rpB) (arB : grB ⊣ rrB)
    {jkA : VA ⥤ WA} {jjA : SA ⥤ ZA} {jkB : VB ⥤ WB} {jjB : SB ⥤ ZB}
    {tv : VA ⥤ VB} {tw : WA ⥤ WB} {ts : SA ⥤ SB} {tz : ZA ⥤ ZB}
    (αA : jjA ⋙ gpA ⟶ grA ⋙ jkA) (αB : jjB ⋙ gpB ⟶ grB ⋙ jkB)
    (hp : tz ⋙ gpB ⟶ gpA ⋙ tw) (hr : ts ⋙ grB ⟶ grA ⋙ tv)
    (mp : rpA ⋙ tz ⟶ tw ⋙ rpB) (mr : rrA ⋙ ts ⟶ tv ⋙ rrB)
    (bk : jkA ⋙ tw ⟶ tv ⋙ jkB) (bj : jjA ⋙ tz ⟶ ts ⋙ jjB)
    (hmp : ∀ N, gpB.map (mp.app N) ≫ apB.counit.app (tw.obj N) =
      hp.app (rpA.obj N) ≫ tw.map (apA.counit.app N))
    (hmr : ∀ N, grB.map (mr.app N) ≫ arB.counit.app (tv.obj N) =
      hr.app (rrA.obj N) ≫ tv.map (arA.counit.app N))
    (hcube : ∀ L, hp.app (jjA.obj L) ≫ tw.map (αA.app L) ≫ bk.app (grA.obj L) =
      gpB.map (bj.app L) ≫ αB.app (ts.obj L) ≫ jkB.map (hr.app L)) (N : VA) :
    tz.map ((mateEquiv arA apA (TwoSquare.mk _ _ _ _ αA)).app N) ≫
        mp.app (jkA.obj N) ≫ rpB.map (bk.app N) =
      bj.app (rrA.obj N) ≫ jjB.map (mr.app N) ≫
        (mateEquiv arB apB (TwoSquare.mk _ _ _ _ αB)).app (tv.obj N) := by
  let γA := (mateEquiv arA apA (TwoSquare.mk _ _ _ _ αA)).natTrans
  let γB := (mateEquiv arB apB (TwoSquare.mk _ _ _ _ αB)).natTrans
  have hga := mateEquiv_counit arA apA (TwoSquare.mk _ _ _ _ αA) N
  have hgb := mateEquiv_counit arB apB (TwoSquare.mk _ _ _ _ αB) (tv.obj N)
  change gpA.map (γA.app N) ≫ apA.counit.app _ =
    αA.app (rrA.obj N) ≫ jkA.map (arA.counit.app N) at hga
  change gpB.map (γB.app (tv.obj N)) ≫ apB.counit.app _ =
    αB.app (rrB.obj (tv.obj N)) ≫ jkB.map (arB.counit.app (tv.obj N)) at hgb
  apply (apB.homEquiv _ _).symm.injective
  change gpB.map (tz.map (γA.app N) ≫ mp.app _ ≫ rpB.map (bk.app N)) ≫
    apB.counit.app _ =
      gpB.map (bj.app _ ≫ jjB.map (mr.app N) ≫ γB.app _) ≫ apB.counit.app _
  have hn := hp.naturality (γA.app N)
  have hb := bk.naturality (arA.counit.app N)
  have hn' := αB.naturality (mr.app N)
  have hc := apB.counit.naturality (bk.app N)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj]
    at hn hb hn' hc ⊢
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, ← Category.assoc (gpB.map (mp.app _)), hmp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← tw.map_comp_assoc, hga]
  simp only [Functor.map_comp, Category.assoc]
  rw [hb]
  rw [reassoc_of% hcube]
  rw [← jkB.map_comp, ← hmr]
  simp only [Functor.map_comp]
  rw [← reassoc_of% hn', ← hgb]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem inverse_mates_naturality
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ C} {U : C ⥤ A} {T : B ⥤ D} {V : D ⥤ B}
    (a : L ⊣ U) (b : T ⊣ V)
    {FA GA : A ⥤ B} {FB GB : C ⥤ D}
    (δF : U ⋙ FA ⟶ FB ⋙ V) (δG : U ⋙ GA ⟶ GB ⋙ V)
    (rA : FA ⟶ GA) (rB : FB ⟶ GB)
    (h : Functor.whiskerLeft U rA ≫ δG = δF ≫ Functor.whiskerRight rB V)
    (M : A) :
    T.map (rA.app M) ≫ ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ δG)).natTrans.app M =
      ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ δF)).natTrans.app M ≫
        rB.app (L.obj M) := by
  let qF := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ δF)).natTrans
  let qG := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ δG)).natTrans
  have hF := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ δF) M
  have hG := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ δG) M
  change FA.map (a.unit.app M) ≫ δF.app (L.obj M) =
    b.unit.app (FA.obj M) ≫ V.map (qF.app M) at hF
  change GA.map (a.unit.app M) ≫ δG.app (L.obj M) =
    b.unit.app (GA.obj M) ≫ V.map (qG.app M) at hG
  have hA := rA.naturality (a.unit.app M)
  change FA.map (a.unit.app M) ≫ rA.app (U.obj (L.obj M)) =
    rA.app M ≫ GA.map (a.unit.app M) at hA
  have hu := b.unit.naturality (rA.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  apply (b.homEquiv _ _).injective
  change b.unit.app (FA.obj M) ≫ V.map (T.map (rA.app M) ≫ qG.app M) =
    b.unit.app (FA.obj M) ≫ V.map (qF.app M ≫ rB.app (L.obj M))
  simp only [Functor.map_comp]
  rw [← reassoc_of% hu, ← hG]
  have hN := congrArg (fun t ↦ t.app (L.obj M)) h
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hN
  rw [← Category.assoc, ← hA, Category.assoc, hN]
  rw [← Category.assoc, hF, Category.assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_mates_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ C} {U : C ⥤ A} {T : B ⥤ D} {V : D ⥤ B}
    (a : L ⊣ U) (b : T ⊣ V) {FA GA : A ⥤ B} {FB GB : C ⥤ D}
    (δF : U ⋙ FA ⟶ FB ⋙ V) (δG : U ⋙ GA ⟶ GB ⋙ V)
    (qF : FA ⋙ T ⟶ L ⋙ FB) (qG : GA ⋙ T ⟶ L ⋙ GB)
    (hqF : qF = ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ δF)).natTrans)
    (hqG : qG = ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ δG)).natTrans)
    (rA : FA ⟶ GA) (rB : FB ⟶ GB)
    (h : Functor.whiskerLeft U rA ≫ δG = δF ≫ Functor.whiskerRight rB V)
    (M : A) : T.map (rA.app M) ≫ qG.app M = qF.app M ≫ rB.app (L.obj M) := by
  rw [hqF, hqG]
  exact inverse_mates_naturality a b δF δG rA rB h M

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem conjugate_whisker_app
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R : A ⥤ B) {F G : B ⥤ C} {H I : A ⥤ C}
    (a : H ≅ R ⋙ F) (b : I ≅ R ⋙ G) (r r' : F ⟶ G) (hr : r = r')
    (s : H ⟶ I) (hs : s = a.hom ≫ Functor.whiskerLeft R r ≫ b.inv) (M : A) :
    s.app M = a.hom.app M ≫ r'.app (R.obj M) ≫ b.inv.app M := by
  rw [hs, hr]
  rfl

private theorem inverse_comparison_square
    {C : Type*} [Category C] {a b c d : C}
    (hc : a ≅ b) (hd : c ≅ d) (r : c ⟶ a) (s : d ⟶ b)
    (h : r ≫ hc.hom = hd.hom ≫ s) : s ≫ hc.inv = hd.inv ≫ r := by
  apply (cancel_mono hc.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem inverse_square
    {A B C : Type*} [Category A] [Category B] [Category C]
    (T : A ⥤ C) (P : B ⥤ C)
    {a b : A} {c d : B} (r : a ≅ b) (s : c ≅ d)
    (qa : T.obj a ⟶ P.obj c) (qb : T.obj b ⟶ P.obj d)
    (h : T.map r.inv ≫ qa = qb ≫ P.map s.inv) :
    qa ≫ P.map s.hom = T.map r.hom ≫ qb := by
  apply (cancel_epi (T.map r.inv)).1
  rw [← Category.assoc, h, Category.assoc, ← P.map_comp, Iso.inv_hom_id,
    P.map_id, Category.comp_id, ← Category.assoc, ← T.map_comp, Iso.inv_hom_id,
    T.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem inverse_square_of_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    (T : A ⥤ C) (P : B ⥤ C) {a b : A} {c d : B}
    (r : a ≅ b) (s : c ≅ d) (ra : b ⟶ a) (sa : d ⟶ c)
    (hr : r.inv = ra) (hs : s.inv = sa)
    (qa : T.obj a ⟶ P.obj c) (qb : T.obj b ⟶ P.obj d)
    (h : T.map ra ≫ qa = qb ≫ P.map sa) :
    qa ≫ P.map s.hom = T.map r.hom ≫ qb := by
  apply inverse_square T P r s
  rw [hr, hs]
  exact h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem limit_square
    {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    (T : A ⥤ B) (P : C ⥤ B) (LA : A ⥤ D) (LB : B ⥤ E) (LC : C ⥤ E)
    (TB : D ⥤ E) (τ : LA ⋙ TB ⟶ T ⋙ LB) (ρ : LC ⟶ P ⋙ LB) [IsIso ρ]
    {a b : A} {c d : C} (r : a ⟶ b) (s : c ⟶ d)
    (qa : T.obj a ⟶ P.obj c) (qb : T.obj b ⟶ P.obj d)
    (h : qa ≫ P.map s = T.map r ≫ qb) :
    (τ.app a ≫ LB.map qa ≫ inv (ρ.app c)) ≫ LC.map s =
      TB.map (LA.map r) ≫ (τ.app b ≫ LB.map qb ≫ inv (ρ.app d)) := by
  have hn := (inv ρ).naturality s
  have ht := τ.naturality r
  dsimp only [Functor.comp_map] at hn ht
  simp only [NatIso.isIso_inv_app] at hn
  simp only [Category.assoc]
  rw [← hn, ← LB.map_comp_assoc, h, LB.map_comp_assoc,
    ← reassoc_of% ht]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem limit_square_of_eq
    {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    (T : A ⥤ B) (P : C ⥤ B) (LA : A ⥤ D) (LB : B ⥤ E) (LC : C ⥤ E)
    (TB : D ⥤ E) (τ : LA ⋙ TB ⟶ T ⋙ LB) (ρ : LC ⟶ P ⋙ LB) [IsIso ρ]
    {a b : A} {c d : C} (r : a ⟶ b) (s : c ⟶ d)
    (qa : T.obj a ⟶ P.obj c) (qb : T.obj b ⟶ P.obj d)
    (za : TB.obj (LA.obj a) ⟶ LC.obj c) (zb : TB.obj (LA.obj b) ⟶ LC.obj d)
    (ha : za = τ.app a ≫ LB.map qa ≫ inv (ρ.app c))
    (hb : zb = τ.app b ≫ LB.map qb ≫ inv (ρ.app d))
    (h : qa ≫ P.map s = T.map r ≫ qb) :
    za ≫ LC.map s = TB.map (LA.map r) ≫ zb := by
  rw [ha, hb]
  exact limit_square T P LA LB LC TB τ ρ r s qa qb h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem transport_square
    {A B C : Type*} [Category A] [Category B] [Category C]
    (T : A ⥤ C) (P : C ⥤ C) (F G : B ⥤ C) (Q : B ⥤ B)
    {a b c d : A} {n m : B} {x y : C}
    (e : a ≅ c) (f : b ≅ d) (g : x ≅ G.obj m) (j : y ≅ F.obj m)
    (r : d ⟶ c) (s : F ⟶ G) (v : n ⟶ Q.obj m)
    (qc : T.obj c ⟶ G.obj n) (qd : T.obj d ⟶ F.obj n)
    (hc : P.obj (G.obj m) ≅ G.obj (Q.obj m))
    (hd : P.obj (F.obj m) ≅ F.obj (Q.obj m))
    (hT : T.map r ≫ qc = qd ≫ s.app n)
    (hP : s.app (Q.obj m) ≫ hc.inv = hd.inv ≫ P.map (s.app m)) :
    T.map (f.hom ≫ r ≫ e.inv) ≫
        (T.map e.hom ≫ qc ≫ G.map v ≫ hc.inv ≫ P.map g.inv) =
      (T.map f.hom ≫ qd ≫ F.map v ≫ hd.inv ≫ P.map j.inv) ≫
        P.map (j.hom ≫ s.app m ≫ g.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% hT, ← reassoc_of% s.naturality v, reassoc_of% hP]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem transport_square_of_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    (T : A ⥤ C) (P : C ⥤ C) (F G : B ⥤ C) (Q : B ⥤ B)
    {a b c d : A} {n m : B} {x y : C}
    (e : a ≅ c) (f : b ≅ d) (g : x ≅ G.obj m) (j : y ≅ F.obj m)
    (r : d ⟶ c) (s : F ⟶ G) (v : n ⟶ Q.obj m)
    (qc : T.obj c ⟶ G.obj n) (qd : T.obj d ⟶ F.obj n)
    (hc : P.obj (G.obj m) ≅ G.obj (Q.obj m))
    (hd : P.obj (F.obj m) ≅ F.obj (Q.obj m))
    (rA : b ⟶ a) (rC : y ⟶ x)
    (za : T.obj a ⟶ P.obj x) (zb : T.obj b ⟶ P.obj y)
    (hrA : rA = f.hom ≫ r ≫ e.inv)
    (hrC : rC = j.hom ≫ s.app m ≫ g.inv)
    (hza : za = T.map e.hom ≫ qc ≫ G.map v ≫ hc.inv ≫ P.map g.inv)
    (hzb : zb = T.map f.hom ≫ qd ≫ F.map v ≫ hd.inv ≫ P.map j.inv)
    (hT : T.map r ≫ qc = qd ≫ s.app n)
    (hP : s.app (Q.obj m) ≫ hc.inv = hd.inv ≫ P.map (s.app m)) :
    T.map rA ≫ za = zb ≫ P.map rC := by
  rw [hrA, hrC, hza, hzb]
  exact transport_square T P F G Q e f g j r s v qc qd hc hd hT hP

section ScalarAlphaGeneric
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] strictScalarPull openTensor gComp jComp jCongr squareG
  jAdj adj betaInv betaInvApp alpha beta

private theorem unit_transpose_injective
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) (X : C) (Y : D) :
    Function.Injective (fun f : F.obj X ⟶ Y ↦ a.unit.app X ≫ G.map f) := by
  intro f g h
  apply (a.homEquiv X Y).injective
  simpa only [Adjunction.homEquiv_unit] using h

private theorem betaInv_cube
    {VA WA SA ZA VB WB SB ZB : Type*}
    [Category VA] [Category WA] [Category SA] [Category ZA]
    [Category VB] [Category WB] [Category SB] [Category ZB]
    {jkA : VA ⥤ WA} {gkA : WA ⥤ VA} {jjA : SA ⥤ ZA} {gjA : ZA ⥤ SA}
    {jkB : VB ⥤ WB} {gkB : WB ⥤ VB} {jjB : SB ⥤ ZB} {gjB : ZB ⥤ SB}
    (unitKA : 𝟭 VA ⟶ jkA ⋙ gkA) (unitJA : 𝟭 SA ⟶ jjA ⋙ gjA)
    (unitKB : 𝟭 VB ⟶ jkB ⋙ gkB) (unitJB : 𝟭 SB ⟶ jjB ⋙ gjB)
    (hinj : ∀ (X : VB) (Y : WB),
      Function.Injective (fun f : jkB.obj X ⟶ Y ↦ unitKB.app X ≫ gkB.map f))
    {grA : SA ⥤ VA} {gpA : ZA ⥤ WA} {grB : SB ⥤ VB} {gpB : ZB ⥤ WB}
    {tv : VA ⥤ VB} {tw : WA ⥤ WB} {ts : SA ⥤ SB} {tz : ZA ⥤ ZB}
    (ek : gkA ⋙ tv ⟶ tw ⋙ gkB) (ej : gjA ⋙ ts ⟶ tz ⋙ gjB)
    (er : grA ⋙ tv ⟶ ts ⋙ grB) (ep : gpA ⋙ tw ⟶ tz ⋙ gpB)
    (bk : jkA ⋙ tw ⟶ tv ⋙ jkB) [IsIso bk] (bj : jjA ⋙ tz ⟶ ts ⋙ jjB)
    (sA : gjA ⋙ grA ⟶ gpA ⋙ gkA) (sB : gjB ⋙ grB ⟶ gpB ⋙ gkB)
    (bA : grA ⋙ jkA ⟶ jjA ⋙ gpA) (bB : grB ⋙ jkB ⟶ jjB ⋙ gpB)
    (huK : dsimp% (∀ Q, tv.map (unitKA.app Q) ≫ ek.app (jkA.obj Q) ≫
      gkB.map (bk.app Q) = unitKB.app (tv.obj Q)))
    (huJ : dsimp% (∀ Q, ts.map (unitJA.app Q) ≫ ej.app (jjA.obj Q) ≫
      gjB.map (bj.app Q) = unitJB.app (ts.obj Q)))
    (hbA : dsimp% (∀ Q, unitKA.app (grA.obj Q) ≫ gkA.map (bA.app Q) =
      grA.map (unitJA.app Q) ≫ sA.app (jjA.obj Q)))
    (hbB : dsimp% (∀ Q, unitKB.app (grB.obj Q) ≫ gkB.map (bB.app Q) =
      grB.map (unitJB.app Q) ≫ sB.app (jjB.obj Q)))
    (hs : dsimp% (∀ Q, tv.map (sA.app Q) ≫ ek.app (gpA.obj Q) ≫ gkB.map (ep.app Q) =
      er.app (gjA.obj Q) ≫ grB.map (ej.app Q) ≫ sB.app (tz.obj Q))) (N : SA) : dsimp% (
    bk.app (grA.obj N) ≫ jkB.map (er.app N) ≫ bB.app (ts.obj N) =
      tw.map (bA.app N) ≫ ep.app (jjA.obj N) ≫ gpB.map (bj.app N) ) := by
  have huK' (Q : VA) : unitKB.app (tv.obj Q) ≫ gkB.map (inv (bk.app Q)) =
      tv.map (unitKA.app Q) ≫ ek.app (jkA.obj Q) := by
    apply ((gkB.mapIso (asIso (bk.app Q))).comp_inv_eq).2
    simpa only [Functor.id_obj, Functor.mapIso_hom, asIso_hom, Category.assoc]
      using (huK Q).symm
  apply (cancel_epi (inv (bk.app (grA.obj N)))).1
  apply hinj _ _
  have hn := ek.naturality (bA.app N)
  have hr := er.naturality (unitJA.app N)
  have hsq := sB.naturality (bj.app N)
  have hu := unitKB.naturality (er.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj]
    at hn hr hsq hu
  rw [IsIso.inv_hom_id_assoc]
  simp only [Functor.map_comp]
  rw [← Category.assoc (unitKB.app _) (gkB.map (inv (bk.app _))), huK']
  simp only [Category.assoc]
  slice_rhs 2 3 => rw [← hn]
  slice_rhs 1 2 => rw [← tv.map_comp, hbA, tv.map_comp]
  slice_rhs 2 4 => rw [hs]
  slice_rhs 1 2 => rw [hr]
  slice_rhs 4 5 => rw [← hsq]
  slice_rhs 2 4 => rw [← grB.map_comp, ← grB.map_comp, huJ]
  slice_lhs 1 2 => rw [← hu]
  slice_lhs 2 3 => rw [hbB]

-- Retain the associators of the library's alpha while doing its scalar calculation
-- in arbitrary categories. The concrete instantiation then needs only type transport.
private def alphaForm
    {H V W S Z : Type*}
    [Category H] [Category V] [Category W] [Category S] [Category Z]
    (u : S ⥤ H) (s : H ⥤ V) (p : V ⥤ H) (q : H ⥤ W)
    (k : V ⥤ W) (r : S ⥤ V) (j : S ⥤ Z) (g : Z ⥤ W)
    (be : j ⋙ g ⟶ u ⋙ q) (pi : 𝟭 H ⟶ s ⋙ p)
    (jc : p ⋙ q ⟶ k) (gc : u ⋙ s ⟶ r) : j ⋙ g ⟶ r ⋙ k :=
  be ≫ Functor.whiskerRight (Functor.whiskerLeft u pi) q ≫
    Functor.whiskerRight (Functor.associator u s p).inv q ≫
    (Functor.associator (u ⋙ s) p q).hom ≫
    Functor.whiskerLeft (u ⋙ s) jc ≫ Functor.whiskerRight gc k

private theorem alpha_pasting
    {HA VA WA SA ZA HB VB WB SB ZB : Type*}
    [Category HA] [Category VA] [Category WA] [Category SA] [Category ZA]
    [Category HB] [Category VB] [Category WB] [Category SB] [Category ZB]
    (th : HA ⥤ HB) (tv : VA ⥤ VB) (tw : WA ⥤ WB) (ts : SA ⥤ SB) (tz : ZA ⥤ ZB)
    (ua : SA ⥤ HA) (sa : HA ⥤ VA) (pa : VA ⥤ HA) (qa : HA ⥤ WA)
    (ka : VA ⥤ WA) (ra : SA ⥤ VA) (ja : SA ⥤ ZA) (ga : ZA ⥤ WA)
    (ub : SB ⥤ HB) (sb : HB ⥤ VB) (pb : VB ⥤ HB) (qb : HB ⥤ WB)
    (kb : VB ⥤ WB) (rb : SB ⥤ VB) (jb : SB ⥤ ZB) (gb : ZB ⥤ WB)
    (hu : ua ⋙ th ≅ ts ⋙ ub) (hs : sa ⋙ tv ≅ th ⋙ sb)
    (hr : ra ⋙ tv ≅ ts ⋙ rb) (hp : ga ⋙ tw ≅ tz ⋙ gb)
    (bs : pa ⋙ th ⟶ tv ⋙ pb) (bq : qa ⋙ tw ⟶ th ⋙ qb)
    (bk : ka ⋙ tw ⟶ tv ⋙ kb) (bj : ja ⋙ tz ⟶ ts ⋙ jb)
    (piA : 𝟭 HA ⟶ sa ⋙ pa) (piB : 𝟭 HB ⟶ sb ⋙ pb)
    (beA : ja ⋙ ga ⟶ ua ⋙ qa) (beB : jb ⋙ gb ⟶ ub ⋙ qb)
    (jcA : pa ⋙ qa ⟶ ka) (jcB : pb ⋙ qb ⟶ kb)
    (gcA : ua ⋙ sa ⟶ ra) (gcB : ub ⋙ sb ⟶ rb)
    (aa : ja ⋙ ga ⟶ ra ⋙ ka) (ab : jb ⋙ gb ⟶ rb ⋙ kb)
    (haa : aa = alphaForm ua sa pa qa ka ra ja ga beA piA jcA gcA)
    (hab : ab = alphaForm ub sb pb qb kb rb jb gb beB piB jcB gcB)
    (hbeta : dsimp% (∀ N, hp.inv.app (ja.obj N) ≫ tw.map (beA.app N) ≫ bq.app (ua.obj N) =
      gb.map (bj.app N) ≫ beB.app (ts.obj N) ≫ qb.map (hu.inv.app N)))
    (hpi : dsimp% (∀ N, th.map (piA.app N) ≫ bs.app (sa.obj N) =
      piB.app (th.obj N) ≫ pb.map (hs.inv.app N)))
    (hopen : dsimp% (∀ N, tw.map (jcA.app N) ≫ bk.app N =
      bq.app (pa.obj N) ≫ qb.map (bs.app N) ≫ jcB.app (tv.obj N)))
    (hpull : dsimp% (∀ N, sb.map (hu.inv.app N) ≫ hs.inv.app (ua.obj N) ≫
      tv.map (gcA.app N) = gcB.app (ts.obj N) ≫ hr.inv.app N)) (N : SA) : dsimp% (
    hp.inv.app (ja.obj N) ≫
        tw.map (aa.app N) ≫
        bk.app (ra.obj N) =
      gb.map (bj.app N) ≫
        ab.app (ts.obj N) ≫
        kb.map (hr.inv.app N) ) := by
  subst aa
  subst ab
  have hk := bk.naturality (gcA.app N)
  have hq := bq.naturality (piA.app (ua.obj N))
  have hj := jcB.naturality (hs.inv.app (ua.obj N))
  have hj' := jcB.naturality (sb.map (hu.inv.app N))
  have hp' := piB.naturality (hu.inv.app N)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj]
    at hk hq hj hj' hp'
  simp only [alphaForm, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app]
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map]
  simp only [Functor.map_comp, qa.map_id, qb.map_id,
    Category.id_comp, Category.assoc]
  slice_lhs 5 6 => rw [hk]
  slice_lhs 4 5 => rw [hopen]
  slice_lhs 3 4 => rw [hq]
  slice_lhs 1 3 => rw [hbeta]
  slice_lhs 4 5 => rw [← qb.map_comp, hpi, qb.map_comp]
  slice_lhs 5 6 => rw [hj]
  slice_lhs 3 4 => rw [← qb.map_comp, hp', qb.map_comp]
  slice_lhs 4 5 => rw [hj']
  slice_lhs 5 7 => rw [← kb.map_comp, ← kb.map_comp, hpull, kb.map_comp]

private theorem pull_cube_hom
    {C : Type*} [Category C] {a b c d e : C}
    (x : a ≅ b) (ca : a ≅ c) (y : c ≅ d) (z : d ≅ e) (cb : b ≅ e)
    (h : cb.hom ≫ z.inv ≫ y.inv = x.inv ≫ ca.hom) :
    ca.hom ≫ y.hom ≫ z.hom = x.hom ≫ cb.hom := by
  apply (cancel_epi x.inv).1
  rw [← reassoc_of% h]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

private theorem beta_cube_of_inverse
    {C : Type*} [Category C] {x y z w v q : C}
    (p : x ⟶ y) (pinv : y ⟶ x) (a : x ⟶ z) (ainv : z ⟶ x)
    (r : w ⟶ v) (rinv : v ⟶ w) (b : q ⟶ v) (binv : v ⟶ q)
    (bk : z ⟶ w) (bj : y ⟶ q)
    (hp : pinv ≫ p = 𝟙 y) (ha : a ≫ ainv = 𝟙 x)
    (hr : r ≫ rinv = 𝟙 w) (hb : binv ≫ b = 𝟙 v)
    (h : bk ≫ r ≫ binv = ainv ≫ p ≫ bj) :
    pinv ≫ a ≫ bk = bj ≫ b ≫ rinv := by
  have hh := congrArg (fun f ↦ pinv ≫ a ≫ f ≫ b ≫ rinv) h
  simp only [Category.assoc] at hh
  rw [← Category.assoc binv b, hb, Category.id_comp, hr, Category.comp_id] at hh
  rw [← Category.assoc a ainv, ha, Category.id_comp,
    ← Category.assoc pinv p, hp, Category.id_comp] at hh
  exact hh

private theorem open_transpose_eq
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) {X : C} {Y : D} (g : X ⟶ G.obj Y) :
    a.unit.app X ≫ G.map ((a.homEquiv X Y).symm g) = g := by
  simpa only [Adjunction.homEquiv_unit] using (a.homEquiv X Y).apply_symm_apply g

private theorem betaInv_unit (A : Type (u + 1)) [CommRing A]
    {V W S Z : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ Z) (j : S ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion j] (h : k ≫ p = r ≫ j)
    (Q : Derived A S) : dsimp% (
    (jAdj A k).unit.app ((G A r).obj Q) ≫
        (G A k).map ((betaInv A r k j p h.symm).app Q) =
      (G A r).map ((jAdj A j).unit.app Q) ≫
        (squareG A r k j p h.symm).inv.app ((J A j).obj Q) ) := by
  exact_congr_type (open_transpose_eq (jAdj A k)
    ((G A r).map ((jAdj A j).unit.app Q) ≫
      (squareG A r k j p h.symm).inv.app ((J A j).obj Q)))

private theorem open_unit_transpose_injective (A : Type (u + 1)) [CommRing A]
    {V W : Scheme.{u}} (k : V ⟶ W) [IsOpenImmersion k]
    (X : Derived A V) (Y : Derived A W) :
    Function.Injective (fun f : (J A k).obj X ⟶ Y ↦
      (jAdj A k).unit.app X ≫ (G A k).map f) := by
  exact_congr_type (unit_transpose_injective (jAdj A k) X Y)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem alpha_eqForm (A : Type (u + 1)) [CommRing A]
    {V W S Z : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ Z) (j : S ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion j] [QuasiCompact k] [QuasiCompact j]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ j) :
    alpha A k r p j h =
      alphaForm (G A (pullback.snd p j)) (G A (squareLift k r p j h))
        (J A (squareLift k r p j h)) (J A (pullback.fst p j))
        (J A k) (G A r) (J A j) (G A p)
        (beta A (pullback.snd p j) (pullback.fst p j) j p pullback.condition.symm
          (IsPullback.of_hasPullback p j).flip).hom
        (pi A (squareLift k r p j h))
        ((jComp A (squareLift k r p j h) (pullback.fst p j)).hom ≫
          (jCongr A (pullback.lift_fst k r h)).hom)
        ((gComp A (squareLift k r p j h) (pullback.snd p j)).inv ≫
          (eqToIso (congrArg (G A) (pullback.lift_snd k r h))).hom) := by
  unfold alpha alphaForm
  rfl

end ScalarAlphaGeneric

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem refinement_scalar_comparison
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    [QuasiCompact c.i] [QuasiCompact d.i] (r : c.Refinement d)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (T l E F i Y).map
        ((compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).app N) ≫
        (comparison l E F i c).app N =
      (comparison l E F i d).app N ≫
        (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r).app
          ((T l E F i X).obj N) := by
  exact scalar_mates_square
    (L := T l E F i X) (U := U l E F i X) (T := T l E F i Y) (V := U l E F i Y)
    (FA := image l E d) (GA := image l E c) (FB := image l F d) (GB := image l F c)
    (scalarAdj l E F i X) (scalarAdj l E F i Y)
    (pastedRestriction l E F i d).hom (pastedRestriction l E F i c).hom
    (comparison l E F i d) (comparison l E F i c)
    (comparison_pasted l E F i d) (comparison_pasted l E F i c)
    (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r)
    (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r)
    (strictRefinementRestrictionSquares l E F i r).1 N

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
include E i in
private theorem refinement_reindex
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    [QuasiCompact c.i] [QuasiCompact d.i] (r : c.Refinement d)
    (e : ℕ) (he : 1 ≤ e)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X) :
    (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r).app
          ((subsequence l F X e).obj N) ≫ (reindexImage l F c e he).inv.app N =
      (reindexImage l F d e he).inv.app N ≫ (subsequence l F Y e).map
        ((compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r).app
          N) := by
  apply inverse_comparison_square ((reindexImage l F c e he).app N)
    ((reindexImage l F d e he).app N)
  have h := congrArg (fun t ↦ t.app N)
    ((strictRefinementRestrictionSquares l E F i r).2 e he)
  exact h

private theorem scalar_composition_pasting
    {C₀ C₁ C₂ C₃ C₄ C₅ D₀ D₁ D₂ D₃ D₄ D₅ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃] [Category C₄] [Category C₅]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃] [Category D₄] [Category D₅]
    (T₀ : C₀ ⥤ D₀) (T₁ : C₁ ⥤ D₁) (T₂ : C₂ ⥤ D₂)
    (T₃ : C₃ ⥤ D₃) (T₄ : C₄ ⥤ D₄) (T₅ : C₅ ⥤ D₅)
    (JA : C₀ ⥤ C₁) (RA : C₁ ⥤ C₂) (IA : C₂ ⥤ C₄) (QA : C₄ ⥤ C₅)
    (LA : C₁ ⥤ C₃) (PA : C₃ ⥤ C₄) (KA : C₀ ⥤ C₃) (HA : C₃ ⥤ C₅)
    (JB : D₀ ⥤ D₁) (RB : D₁ ⥤ D₂) (IB : D₂ ⥤ D₄) (QB : D₄ ⥤ D₅)
    (LB : D₁ ⥤ D₃) (PB : D₃ ⥤ D₄) (KB : D₀ ⥤ D₃) (HB : D₃ ⥤ D₅)
    (qJ : JA ⋙ T₁ ⟶ T₀ ⋙ JB) (qR : RA ⋙ T₂ ⟶ T₁ ⋙ RB)
    (qI : IA ⋙ T₄ ⟶ T₂ ⋙ IB) (qQ : QA ⋙ T₅ ⟶ T₄ ⋙ QB)
    (qL : LA ⋙ T₃ ⟶ T₁ ⋙ LB) (qP : PA ⋙ T₄ ⟶ T₃ ⋙ PB)
    (qK : KA ⋙ T₃ ⟶ T₀ ⋙ KB) (qH : HA ⋙ T₅ ⟶ T₃ ⋙ HB)
    (γA : RA ⋙ IA ⟶ LA ⋙ PA) (γB : RB ⋙ IB ⟶ LB ⋙ PB)
    (jA : JA ⋙ LA ⟶ KA) (jB : JB ⋙ LB ⟶ KB)
    (rA : PA ⋙ QA ⟶ HA) (rB : PB ⋙ QB ⟶ HB)
    (hj : ∀ M, T₃.map (jA.app M) ≫ qK.app M =
      qL.app (JA.obj M) ≫ LB.map (qJ.app M) ≫ jB.app (T₀.obj M))
    (hr : ∀ M, T₅.map (rA.app M) ≫ qH.app M =
      qQ.app (PA.obj M) ≫ QB.map (qP.app M) ≫ rB.app (T₃.obj M))
    (hγ : ∀ M, T₄.map (γA.app M) ≫ qP.app (LA.obj M) ≫ PB.map (qL.app M) =
      qI.app (RA.obj M) ≫ IB.map (qR.app M) ≫ γB.app (T₁.obj M))
    (M : C₀) :
    T₅.map (QA.map (γA.app (JA.obj M)) ≫
        QA.map (PA.map (jA.app M)) ≫ rA.app (KA.obj M)) ≫
        qH.app (KA.obj M) ≫ HB.map (qK.app M) =
      (qQ.app (IA.obj (RA.obj (JA.obj M))) ≫ QB.map (qI.app (RA.obj (JA.obj M))) ≫
        QB.map (IB.map (qR.app (JA.obj M))) ≫
        QB.map (IB.map (RB.map (qJ.app M)))) ≫
      QB.map (γB.app (JB.obj (T₀.obj M))) ≫
        QB.map (PB.map (jB.app (T₀.obj M))) ≫ rB.app (KB.obj (T₀.obj M)) := by
  have hn₁ := qQ.naturality (PA.map (jA.app M))
  have hn₂ := qQ.naturality (γA.app (JA.obj M))
  have hn₃ := qP.naturality (jA.app M)
  have hn₄ := rB.naturality (qK.app M)
  have hn₅ := γB.naturality (qJ.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₁ hn₂ hn₃ hn₄ hn₅
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hr, ← hn₄, reassoc_of% hn₁, reassoc_of% hn₂]
  simp only [← QB.map_comp_assoc]
  rw [reassoc_of% hn₃]
  rw [← PB.map_comp, hj]
  simp only [PB.map_comp]
  rw [reassoc_of% hγ, ← reassoc_of% hn₅]


private theorem clopen_scalar_projection_of_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {GA : A ⥤ B} {JA : B ⥤ A} {GB : C ⥤ D} {JB RB : D ⥤ C}
    (b : GB ⊣ RB) (ja : JA ⊣ GA) (jb : JB ⊣ GB)
    (o : JB ≅ RB) (TA : A ⥤ C) (TB : B ⥤ D)
    (h : GA ⋙ TB ≅ TA ⋙ GB) (t : JA ⋙ TA ⟶ TB ⋙ JB)
    (pa : 𝟭 A ⟶ GA ⋙ JA) (pb : 𝟭 C ⟶ GB ⋙ JB)
    (hpa : ∀ N, GA.map (pa.app N) = ja.unit.app (GA.obj N))
    (hpb : ∀ N, GB.map (pb.app N) = jb.unit.app (GB.obj N))
    (hu : ∀ M, TB.map (ja.unit.app M) ≫ h.hom.app (JA.obj M) ≫
      GB.map (t.app M) = jb.unit.app (TB.obj M)) (N : A) :
    TA.map (pa.app N) ≫ t.app (GA.obj N) =
      pb.app (TA.obj N) ≫ JB.map (h.inv.app N) := by
  have he : GB.map (TA.map (pa.app N) ≫ t.app (GA.obj N)) =
      GB.map (pb.app (TA.obj N) ≫ JB.map (h.inv.app N)) := by
    have hn := h.hom.naturality (pa.app N)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    apply (cancel_epi (h.hom.app N)).1
    simp only [Functor.map_comp, ← Category.assoc]
    rw [← hn]
    simp only [Category.assoc]
    rw [hpa, hu]
    have hj := jb.unit.naturality (h.inv.app N)
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hj
    rw [hpb, ← hj]
    rw [Iso.hom_inv_id_app_assoc]
  apply (cancel_mono (o.hom.app (TB.obj (GA.obj N)))).1
  apply (b.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ z ≫ GB.map (o.hom.app (TB.obj (GA.obj N))) ≫
      b.counit.app (TB.obj (GA.obj N))) he

/-- Constant tensor carries the intrinsic clopen projection to the same projection.
Source: Stacks 0E8I, 09AE; auxiliary Step 5
(blueprint: lem-pur-compact-support-strict-scalar-refinement).
Proof: in the section/complement decomposition, both maps send (x,y) tensor b to
(x tensor b,0). Balanced pure tensors generate locally. These are equal maps of
complexes of strict B-towers, compatible with differentials and every transition;
exact localization retains their equality, without a faithfulness claim for ev. -/
theorem scalar_clopen_projection {U W : Scheme.{u}} (s : U ⟶ W)
    [IsOpenImmersion s] [IsClosedImmersion s]
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
    (T l E F i W).map
        ((pi (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) s).app N) ≫
        (openTensor l E F i s).app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) s).obj N) =
      (pi (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) s).app
          ((T l E F i W).obj N) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) s).map
          ((strictScalarPull l E F i s).inv.app N) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  let O : W.Opens := ⟨(Set.range s)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have ho := openToR_isIso B s
  exact clopen_scalar_projection_of_unit (adj B s) (jAdj A s) (jAdj B s)
    (asIso (openToR B s)) (T l E F i W) (T l E F i U)
    (strictScalarPull l E F i s) (openTensor l E F i s) (pi A s) (pi B s)
    (fun Q ↦ (pi_components A s O.ι (Scheme.Opens.range_ι O) Q).1)
    (fun Q ↦ (pi_components B s O.ι (Scheme.Opens.range_ι O) Q).1)
    (strictScalarOpenUnit l E F i s) N

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_jComp_named {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion k] (h : f ≫ g = k)
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (T l E F i Z).map
        (((jComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).hom ≫
          (jCongr (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) h).hom).app M) ≫
        (openTensor l E F i k).app M =
      (openTensor l E F i g).app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f).obj M) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g).map
          ((openTensor l E F i f).app M) ≫
        (((jComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).hom ≫
          (jCongr (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) h).hom).app
            ((T l E F i X).obj M)) := by
  subst k
  simpa only [jCongr, eqToIso_refl, Iso.refl_hom, NatTrans.comp_app,
    NatTrans.id_app, Category.comp_id] using strictScalarOpenComposition l E F i f g M

section ScalarAlpha
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] strictScalarPull openTensor gComp jComp jCongr squareG
  jAdj adj betaInv betaInvApp alpha beta

private theorem scalar_gComp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (T l E F i X).map
        ((gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).hom.app M) ≫
        (strictScalarPull l E F i f).hom.app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj M) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f).map
          ((strictScalarPull l E F i g).hom.app M) =
      (strictScalarPull l E F i (f ≫ g)).hom.app M ≫
        (gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).hom.app
          ((T l E F i Z).obj M) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  have_cast_args h := pull_cube_hom
    ((strictScalarPull l E F i (f ≫ g)).app M)
    ((T l E F i X).mapIso ((gComp A f g).app M))
    ((strictScalarPull l E F i f).app ((G A g).obj M))
    ((G B f).mapIso ((strictScalarPull l E F i g).app M))
    ((gComp B f g).app ((T l E F i Z).obj M))
    (strictScalarPullComposition l E F i f g M)
  exact_congr_type h

private theorem scalar_gComp_inv_named {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f).map
          ((strictScalarPull l E F i g).inv.app M) ≫
        (strictScalarPull l E F i f).inv.app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj M) ≫
        (T l E F i X).map
          (((gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).inv ≫
            (eqToIso (congrArg
              (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) h)).hom).app M) =
      (((gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).inv ≫
          (eqToIso (congrArg
            (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F))) h)).hom).app
              ((T l E F i Z).obj M)) ≫
        (strictScalarPull l E F i k).inv.app M := by
  subst k
  dsimp only [eqToIso_refl, Iso.refl_hom, NatTrans.comp_app, NatTrans.id_app]
  simp only [Category.comp_id]
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  have_cast_args h := inverse_comparison_square
    ((T l E F i X).mapIso ((gComp A f g).app M))
    ((gComp B f g).app ((T l E F i Z).obj M))
    ((strictScalarPull l E F i (f ≫ g)).inv.app M)
    ((G B f).map ((strictScalarPull l E F i g).inv.app M) ≫
      (strictScalarPull l E F i f).inv.app ((G A g).obj M))
    (strictScalarPullComposition l E F i f g M).symm
  dsimp only [Functor.mapIso, Iso.app] at h
  simp only [Category.assoc] at h
  exact_congr_type h

private theorem scalar_gComp_named {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (T l E F i X).map
        (((gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).inv ≫
          (eqToIso (congrArg
            (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) h.symm)).inv).app M) ≫
        (strictScalarPull l E F i k).hom.app M =
      (strictScalarPull l E F i f).hom.app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj M) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f).map
          ((strictScalarPull l E F i g).hom.app M) ≫
        (((gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).inv ≫
          (eqToIso (congrArg
            (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F))) h.symm)).inv).app
              ((T l E F i Z).obj M)) := by
  subst k
  dsimp only [eqToIso_refl, Iso.refl_inv, NatTrans.comp_app, NatTrans.id_app]
  simp only [Category.comp_id]
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  have_cast_args h := inverse_comparison_square
    ((gComp B f g).app ((T l E F i Z).obj M))
    ((T l E F i X).mapIso ((gComp A f g).app M))
    ((strictScalarPull l E F i (f ≫ g)).hom.app M)
    ((strictScalarPull l E F i f).hom.app ((G A g).obj M) ≫
      (G B f).map ((strictScalarPull l E F i g).hom.app M))
    (scalar_gComp_hom l E F i f g M).symm
  dsimp only [Functor.mapIso, Iso.app] at h
  simp only [Category.assoc] at h
  exact_congr_type h.symm

private theorem square_scalar_pasting
    {C : Type*} [Category C] {x y z p q r : C}
    (a : x ⟶ y) (b : y ⟶ z) (c : z ⟶ p) (d : p ⟶ q)
    (e : y ⟶ r) (f : r ⟶ q) (g : x ⟶ r)
    (hm : b ≫ c ≫ d = e ≫ f) (hn : a ≫ e = g) :
    a ≫ b ≫ c ≫ d = g ≫ f := by
  rw [hm, ← Category.assoc, hn]

private theorem scalar_squareG_inv {V W S Z : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ Z) (j : S ⟶ Z)
    (h : k ≫ p = r ≫ j)
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) : dsimp% (
    (T l E F i V).map
        ((squareG (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p
          h.symm).inv.app M) ≫
        (strictScalarPull l E F i k).hom.app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) p).obj M) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map
          ((strictScalarPull l E F i p).hom.app M) =
      (strictScalarPull l E F i r).hom.app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj M) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r).map
          ((strictScalarPull l E F i j).hom.app M) ≫
        (squareG (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p
          h.symm).inv.app ((T l E F i Z).obj M) ) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  have_cast_args hpaste := square_scalar_pasting
    ((T l E F i V).map
      (((gComp A r j).inv ≫ (eqToIso (congrArg (G A) h)).inv).app M))
    ((T l E F i V).map ((gComp A k p).hom.app M))
    ((strictScalarPull l E F i k).hom.app ((G A p).obj M))
    ((G B k).map ((strictScalarPull l E F i p).hom.app M))
    ((strictScalarPull l E F i (k ≫ p)).hom.app M)
    ((gComp B k p).hom.app ((T l E F i Z).obj M))
    ((strictScalarPull l E F i r).hom.app ((G A j).obj M) ≫
      (G B r).map ((strictScalarPull l E F i j).hom.app M) ≫
      (((gComp B r j).inv ≫ (eqToIso (congrArg (G B) h)).inv).app
        ((T l E F i Z).obj M)))
    (scalar_gComp_hom l E F i k p M)
    (scalar_gComp_named l E F i r j (k ≫ p) h.symm M)
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc] at hpaste
  simp only [squareG, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  exact_congr_type hpaste

private theorem scalar_open_isIso {V W : Scheme.{u}} (k : V ⟶ W)
    [IsOpenImmersion k] : IsIso (openTensor l E F i k) := by
  rw [openTensor_ordinary]
  exact_congr_type (Functor.mapDerivedCategorySquareIso
    (@asIso _ _ _ _ (ordinaryOpenTensor l E F i k)
      (ordinaryOpenTensor_isIso l E F i k))).isIso_hom

private theorem scalar_open_unit {V W : Scheme.{u}} (k : V ⟶ W)
    [IsOpenImmersion k]
    (Q : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) V) : dsimp% (
    (T l E F i V).map
        ((jAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k).unit.app Q) ≫
        (strictScalarPull l E F i k).hom.app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k).obj Q) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map
          ((openTensor l E F i k).app Q) =
      (jAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).unit.app
        ((T l E F i V).obj Q) ) := by
  exact_congr_type (strictScalarOpenUnit l E F i k Q)

private theorem scalar_betaInv {V W S Z : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ Z) (j : S ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion j] (h : k ≫ p = r ≫ j)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) S) : dsimp% (
    (openTensor l E F i k).app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).obj N) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map
          ((strictScalarPull l E F i r).hom.app N) ≫
        (betaInv (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p
          h.symm).app ((T l E F i S).obj N) =
      (T l E F i W).map
          ((betaInv (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p
            h.symm).app N) ≫
        (strictScalarPull l E F i p).hom.app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N) ≫
        (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) p).map
          ((openTensor l E F i j).app N) ) := by
  have := scalar_open_isIso l E F i k
  have hc := betaInv_cube
    (jAdj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k).unit (jAdj (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) j).unit (jAdj (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F)) k).unit (jAdj (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F)) j).unit
    (open_unit_transpose_injective (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k)
    (strictScalarPull l E F i k).hom (strictScalarPull l E F i j).hom
    (strictScalarPull l E F i r).hom (strictScalarPull l E F i p).hom
    (openTensor l E F i k) (openTensor l E F i j)
    (squareG (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p h.symm).inv (squareG
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p h.symm).inv
    (betaInv (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p h.symm) (betaInv
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p h.symm)
    (scalar_open_unit l E F i k) (scalar_open_unit l E F i j)
    (betaInv_unit (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k r p j h) (betaInv_unit
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k r p j h)
    (scalar_squareG_inv l E F i k r p j h) N
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `hc
      | Lean.throwError "missing beta compatibility proof"
    (← Lean.Elab.Tactic.getMainGoal).assign hd.toExpr
    Lean.Elab.Tactic.replaceMainGoal []

private theorem scalar_beta {V W S Z : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ Z) (j : S ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (h : k ≫ p = r ≫ j) (hsq : IsPullback k r p j)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) S) : dsimp% (
    (strictScalarPull l E F i p).inv.app
        ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N) ≫
        (T l E F i W).map
          ((beta (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p
            h.symm hsq.flip).hom.app N) ≫
        (openTensor l E F i k).app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).obj N) =
      (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) p).map
          ((openTensor l E F i j).app N) ≫
        (beta (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p
          h.symm hsq.flip).hom.app ((T l E F i S).obj N) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map
          ((strictScalarPull l E F i r).inv.app N) ) := by
  have hc := scalar_betaInv l E F i k r p j h N
  have ha : (beta (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p h.symm
    hsq.flip).inv = betaInv (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p h.symm
    := by unfold beta; rfl
  have hb : (beta (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p h.symm
    hsq.flip).inv = betaInv (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p h.symm
    := by unfold beta; rfl
  have hpa := Iso.inv_hom_id_app (strictScalarPull l E F i p)
    ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N)
  have haa := congrArg ((T l E F i W).map)
    (Iso.hom_inv_id_app (beta
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p h.symm hsq.flip) N)
  rw [ha] at haa
  simp only [Functor.map_comp, (T l E F i W).map_id] at haa
  have hra := congrArg ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map)
    (Iso.hom_inv_id_app (strictScalarPull l E F i r) N)
  simp only [Functor.map_comp,
    (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map_id] at hra
  have hba := Iso.inv_hom_id_app (beta
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p h.symm hsq.flip)
    ((T l E F i S).obj N)
  rw [hb] at hba
  have_cast_args hd := beta_cube_of_inverse
    (x := (T l E F i W).obj
      ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) p).obj
        ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N)))
    (y := (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) p).obj
      ((T l E F i Z).obj
        ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N)))
    (z := (T l E F i W).obj
      ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k).obj
        ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).obj N)))
    (w := (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).obj
      ((T l E F i V).obj
        ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).obj N)))
    (v := (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).obj
      ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r).obj
        ((T l E F i S).obj N)))
    (q := (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) p).obj
      ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j).obj
        ((T l E F i S).obj N)))
    ((strictScalarPull l E F i p).hom.app
      ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N))
    ((strictScalarPull l E F i p).inv.app
      ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N))
    ((T l E F i W).map ((beta
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p h.symm hsq.flip).hom.app N))
    ((T l E F i W).map ((betaInv
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r k j p h.symm).app N))
    ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map
      ((strictScalarPull l E F i r).hom.app N))
    ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map
      ((strictScalarPull l E F i r).inv.app N))
    ((beta (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p h.symm
      hsq.flip).hom.app ((T l E F i S).obj N))
    ((betaInv (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r k j p h.symm).app
      ((T l E F i S).obj N))
    ((openTensor l E F i k).app
      ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).obj N))
    ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) p).map
      ((openTensor l E F i j).app N)) hpa haa hra hba hc
  exact_congr_type hd

end ScalarAlpha

section ScalarAlphaFinal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] strictScalarPull openTensor gComp jComp jCongr squareG
  jAdj adj betaInv betaInvApp alpha beta alphaForm

-- Assemble the exact factors in a private, fully proved helper.
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem scalar_properOpen_alpha_core {V W S Z : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ Z) (j : S ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion j] [QuasiCompact k] [QuasiCompact j]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ j)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) S) :
    (strictScalarPull l E F i p).inv.app
        ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N) ≫
        (T l E F i W).map
          ((alpha (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k r p j h).app
            N) ≫
        (openTensor l E F i k).app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).obj N) =
      (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) p).map
          ((openTensor l E F i j).app N) ≫
        (alpha (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k r p j h).app
          ((T l E F i S).obj N) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map
          ((strictScalarPull l E F i r).inv.app N) := by
  have_cast_args hdata := alpha_pasting
    (HA := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) (pullback p j))
    (VA := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) V)
    (WA := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W)
    (SA := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) S)
    (ZA := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z)
    (HB := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) (pullback p j))
    (VB := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) V)
    (WB := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W)
    (SB := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) S)
    (ZB := Derived
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) Z)
    (T l E F i (pullback p j)) (T l E F i V) (T l E F i W)
    (T l E F i S) (T l E F i Z)
    (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) (pullback.snd p j)) (G (ULift.{u +
      1} (Padic.coefficientExtensionIntegers l E)) (squareLift k r p j h)) (J (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) (squareLift k r p j h)) (J (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) (pullback.fst p j)) (J (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) k) (G (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) r) (J (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) j) (G (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) p)
    (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) (pullback.snd p j)) (G (ULift.{u +
      1} (Padic.coefficientExtensionIntegers l F)) (squareLift k r p j h)) (J (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F)) (squareLift k r p j h)) (J (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F)) (pullback.fst p j)) (J (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F)) k) (G (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F)) r) (J (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F)) j) (G (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F)) p)
    (strictScalarPull l E F i (pullback.snd p j)) (strictScalarPull l E F i (squareLift k r p j h))
    (strictScalarPull l E F i r) (strictScalarPull l E F i p)
    (openTensor l E F i (squareLift k r p j h)) (openTensor l E F i (pullback.fst p j))
    (openTensor l E F i k) (openTensor l E F i j) (pi (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E)) (squareLift k r p j h)) (pi (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F)) (squareLift k r p j h))
    (beta (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) (pullback.snd p j) (pullback.fst
      p j) j p pullback.condition.symm (IsPullback.of_hasPullback p j).flip).hom
    (beta (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) (pullback.snd p j) (pullback.fst
      p j) j p pullback.condition.symm (IsPullback.of_hasPullback p j).flip).hom
    ((jComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) (squareLift k r p j h)
      (pullback.fst p j)).hom ≫ (jCongr (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (pullback.lift_fst k r h)).hom)
    ((jComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) (squareLift k r p j h)
      (pullback.fst p j)).hom ≫ (jCongr (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F))
      (pullback.lift_fst k r h)).hom)
    ((gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) (squareLift k r p j h)
      (pullback.snd p j)).inv ≫ (eqToIso (congrArg (G (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l E))) (pullback.lift_snd k r h))).hom)
    ((gComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) (squareLift k r p j h)
      (pullback.snd p j)).inv ≫ (eqToIso (congrArg (G (ULift.{u + 1}
      (Padic.coefficientExtensionIntegers l F))) (pullback.lift_snd k r h))).hom)
    (alpha (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k r p j h)
    (alpha (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k r p j h)
  have_cast_args hforms := hdata
    (by exact_congr_type
      (alpha_eqForm (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k r p j h))
    (by exact_congr_type
      (alpha_eqForm (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k r p j h))
  have_cast_args hpaste := hforms
    (by
      intro M
      exact_congr_type (scalar_beta l E F i (pullback.fst p j) (pullback.snd p j) p j
        pullback.condition (IsPullback.of_hasPullback p j) M))
    (by
      intro M
      exact_congr_type (scalar_clopen_projection l E F i (squareLift k r p j h) M))
    (by
      intro M
      exact_congr_type (scalar_jComp_named l E F i (squareLift k r p j h)
        (pullback.fst p j) k (pullback.lift_fst k r h) M))
    (by
      intro M
      exact_congr_type (scalar_gComp_inv_named l E F i (squareLift k r p j h)
        (pullback.snd p j) r (pullback.lift_snd k r h) M)) N
  exact_congr_type hpaste

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The scalar cube for the specified beta/projection alpha, including noncartesian squares.
Source: Stacks 0F7B and 0E8I; auxiliary Steps 3--5
(blueprint: lem-pur-compact-support-strict-scalar-refinement).
Proof: transpose inverse beta under the open adjunction. Tensor preserves its open
unit, identity on each open summand, so the beta square commutes. Tensor preserves
pi by scalar_clopen_projection, including zero on the complementary component.
Paste with open composition, which preserves the same summands. The resulting
cube equation is an equality before evaluation or inverse limit. -/
theorem scalar_properOpen_alpha {V W S Z : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ Z) (j : S ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion j] [QuasiCompact k] [QuasiCompact j]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ j)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) S) :
    (strictScalarPull l E F i p).inv.app
        ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N) ≫
        (T l E F i W).map
          ((alpha (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k r p j h).app
            N) ≫
        (openTensor l E F i k).app
          ((G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).obj N) =
      (G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) p).map
          ((openTensor l E F i j).app N) ≫
        (alpha (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k r p j h).app
          ((T l E F i S).obj N) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k).map
          ((strictScalarPull l E F i r).inv.app N) := by
  exact_congr_type (scalar_properOpen_alpha_core l E F i k r p j h N)

end ScalarAlphaFinal

/-- Ordered proper mates of the scalar cube agree for every commutative proper/open square.
Source: Stacks 07A6, 0F7B--0F7D; auxiliary Step 6
(blueprint: lem-pur-compact-support-strict-scalar-refinement).
Proof: take the two proper-adjunction mates of scalar_properOpen_alpha. Apply
mateEquiv_vcomp and mateEquiv_hcomp. The mates of the pullback scalar comparisons
are proper, with transpose tensor of the geometric counit, and the mates of alpha
are the recorded gamma. Composite adjunctions retain the ordered unit and counit.
Thus the two pasted maps are equal in D(Tow(Mod(B))). This applies also to each
horizontal or vertical pasted square of normalizedProperOpenCalculus. -/
theorem scalar_properOpen_gamma {V W S Z : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ Z) (j : S ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion j] [QuasiCompact k] [QuasiCompact j]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ j)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) V) :
    (T l E F i Z).map
        ((gamma (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k r p j h).app
          N) ≫
        (proper l E F i p).app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k).obj N) ≫
        (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) p).map
          ((openTensor l E F i k).app N) =
      (openTensor l E F i j).app
          ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).obj N) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) j).map
          ((proper l E F i r).app N) ≫
        (gamma (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k r p j h).app
          ((T l E F i V).obj N) := by
  exact scalar_cube_mates
    (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) p)
    (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r)
    (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) p)
    (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r)
    (alpha (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) k r p j h)
    (alpha (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) k r p j h)
    (strictScalarPull l E F i p).inv (strictScalarPull l E F i r).inv
    (proper l E F i p) (proper l E F i r)
    (openTensor l E F i k) (openTensor l E F i j)
    (strictProper_geometric_transpose l E F i p)
    (strictProper_geometric_transpose l E F i r)
    (scalar_properOpen_alpha l E F i k r p j h) N

/-- Theta is the recorded normalized constant-tower refinement comparison, transported
through the unit-normalized native support-model isomorphisms. Its direction is d to c.
Source: Stacks 0F7B--0F7D; auxiliary Step 7
(blueprint: lem-pur-compact-support-strict-scalar-refinement). -/
def supportRefinement {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    support l E d S ⟶ support l E c S :=
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  letI : QuasiCompact d.i := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  (supportModel l E d S).hom ≫
    Functor.whiskerLeft (reduction l E X S)
      (AlgebraicGeometry.ProEtale.StrictTower.compositionC
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r) ≫
    (supportModel l E c S).inv

attribute [local irreducible] supportRefinement supportModel reduction support

private theorem supportRefinement_eq
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    supportRefinement l E r S = (supportModel l E d S).hom ≫
      Functor.whiskerLeft (reduction l E X S)
        (refinementComparison (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r) ≫
      (supportModel l E c S).inv := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  let : QuasiCompact d.i := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  unfold supportRefinement
  rw [comparison_eq]

/-- On finite-etale-origin inputs Theta is invertible, with no common lower bound.
Source: Stacks 0F7B; auxiliary Steps 1--2, 7--8
(blueprint: lem-pur-compact-support-strict-scalar-refinement).
Proof: refinementComparison_isIso applies to each supplied finite origin separately.
Whisker that component with reduction, then conjugate by supportModel. Both model
maps are isomorphisms, so the result is invertible in the strict derived category. -/
theorem supportRefinement_isIso {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M)))) :
    IsIso ((supportRefinement l E r S).app M) := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  let : QuasiCompact d.i := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f)
  apply conjugate_app_isIso (supportModel l E d S)
    (Functor.whiskerLeft (reduction l E X S)
      (refinementComparison (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r))
    (supportModel l E c S) (supportRefinement l E r S) ?_ M
  · exact @refinementComparison_isIso.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) _ X Y f c d r
      ((reduction l E X S).obj M) hM (inferInstance : QuasiCompact f)
  · unfold supportRefinement
    rw [comparison_eq]

/-- Rho is precisely inverse Theta, never a freely chosen comparison isomorphism.
Source: Stacks 0F7B; auxiliary Step 8
(blueprint: lem-pur-compact-support-strict-scalar-refinement). -/
def supportRefinementIso {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M)))) :
    (support l E c S).obj M ≅ (support l E d S).obj M :=
  haveI := supportRefinement_isIso l E r S M hM
  (asIso ((supportRefinement l E r S).app M)).symm

private theorem supportRefinementIso_inv
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M)))) :
    (supportRefinementIso l E r S M hM).inv = (supportRefinement l E r S).app M := by
  dsimp only [supportRefinementIso, Iso.symm_inv, asIso_hom]

private theorem supportRefinement_identity
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M))))
    (c : Compactification f) :
    (supportRefinement l E (Compactification.Refinement.id c) S).app M = 𝟙 _ := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : IsSeparated f := c.isSeparated
  have : LocallyOfFiniteType f := c.locallyOfFiniteType
  have h := (@refinementExchangeCoherence.{u} A _ X Y f
    inferInstance inferInstance inferInstance ((reduction l E X S).obj M) hM).2.1 c
  have ht : supportRefinement l E (Compactification.Refinement.id c) S = 𝟙 _ := by
    calc
      supportRefinement l E (Compactification.Refinement.id c) S =
          (supportModel l E c S).hom ≫ (𝟙 _) ≫ (supportModel l E c S).inv := by
        rw [supportRefinement_eq, h]
        rfl
      _ = 𝟙 _ := by rw [Category.id_comp, Iso.hom_inv_id]
  exact NatTrans.congr_app ht M

private theorem supportRefinement_composition
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M))))
    (c d b : Compactification f) (r : c.Refinement d) (s : d.Refinement b) :
    (supportRefinement l E (r.comp s) S).app M =
      (supportRefinement l E s S).app M ≫ (supportRefinement l E r S).app M := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  let : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  let : QuasiCompact b.i := b.quasiCompact_openImmersion inferInstance
  have : IsSeparated f := c.isSeparated
  have : LocallyOfFiniteType f := c.locallyOfFiniteType
  have h := (@refinementExchangeCoherence.{u} A _ X Y f
    inferInstance inferInstance inferInstance ((reduction l E X S).obj M) hM).2.2.1 r s
  have ht : supportRefinement l E (r.comp s) S =
      supportRefinement l E s S ≫ supportRefinement l E r S := by
    rw [supportRefinement_eq, supportRefinement_eq l E s S,
      supportRefinement_eq l E r S, h, Functor.whiskerLeft_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  exact NatTrans.congr_app ht M

/-- Identity and composition of rho use the normalized comparison, before taking limits.
Source: Stacks 0F7C--0F7D; auxiliary Step 9
(blueprint: lem-pur-compact-support-strict-scalar-refinement).
Proof: conjugate refinementComparison_id and refinementComparison_comp by
supportModel. Cancel the adjacent model maps. Invert the resulting identity and
composition equations, retaining their order. This is an equality of strict-tower
isomorphisms; it is not inferred by testing finite evaluations. -/
theorem supportRefinementIso_coherence {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M)))) :
    (∀ c : Compactification f,
      supportRefinementIso l E (Compactification.Refinement.id c) S M hM = Iso.refl _) ∧
    ∀ (c d b : Compactification f) (r : c.Refinement d) (s : d.Refinement b),
      supportRefinementIso l E (r.comp s) S M hM =
        supportRefinementIso l E r S M hM ≪≫ supportRefinementIso l E s S M hM := by
  constructor
  · intro c
    apply Iso.ext_inv
    rw [supportRefinementIso_inv]
    simpa only [Iso.refl_inv] using supportRefinement_identity l E S M hM c
  · intro c d b r s
    apply Iso.ext_inv
    dsimp only [Iso.trans_inv]
    rw [supportRefinementIso_inv, supportRefinementIso_inv, supportRefinementIso_inv]
    simpa only [] using supportRefinement_composition l E S M hM c d b r s

/-- The common-refinement comparison is inverse rho along the first arrow, then rho
along the second. Source: Stacks 0F7C; auxiliary Step 9
(blueprint: lem-pur-compact-support-strict-scalar-refinement). -/
def supportCommonRefinementIso {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d b : Compactification f} (r : b.Refinement c) (s : b.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M)))) :
    (support l E c S).obj M ≅ (support l E d S).obj M :=
  (supportRefinementIso l E r S M hM).symm ≪≫ supportRefinementIso l E s S M hM

private theorem supportCommonRefinementIso_hom {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d b : Compactification f} (r : b.Refinement c) (s : b.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M)))) :
    (supportCommonRefinementIso l E r s S M hM).hom =
      (supportRefinementIso l E r S M hM).inv ≫
        (supportRefinementIso l E s S M hM).hom := by
  rfl

attribute [local irreducible] supportRefinementIso

private theorem supportRefinementIso_parallel
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M))))
    {c d : Compactification f} (r s : c.Refinement d) :
    supportRefinementIso l E r S M hM = supportRefinementIso l E s S M hM := by
  obtain ⟨b, t, ht⟩ := IsCofilteredOrEmpty.cone_maps (C := Compactification f)
    (r : c ⟶ d) (s : c ⟶ d)
  have ht' : t.comp r = t.comp s := ht
  have hh := congrArg (fun a ↦ supportRefinementIso l E a S M hM) ht'
  rw [(supportRefinementIso_coherence l E S M hM).2 b c d t r,
    (supportRefinementIso_coherence l E S M hM).2 b c d t s] at hh
  apply Iso.ext
  exact (cancel_epi (supportRefinementIso l E t S M hM).hom).1
    (congrArg Iso.hom hh)

private theorem supportCommonRefinementIso_refine
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M))))
    {c d b a : Compactification f} (r : b.Refinement c) (s : b.Refinement d)
    (t : a.Refinement b) :
    supportCommonRefinementIso l E (t.comp r) (t.comp s) S M hM =
      supportCommonRefinementIso l E r s S M hM := by
  unfold supportCommonRefinementIso
  rw [(supportRefinementIso_coherence l E S M hM).2 a b c t r,
    (supportRefinementIso_coherence l E S M hM).2 a b d t s]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Category.assoc,
    Iso.inv_hom_id_assoc]

private theorem supportCommonRefinementIso_independent
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M))))
    {c d b b' : Compactification f} (r : b.Refinement c) (s : b.Refinement d)
    (r' : b'.Refinement c) (s' : b'.Refinement d) :
    supportCommonRefinementIso l E r s S M hM =
      supportCommonRefinementIso l E r' s' S M hM := by
  obtain ⟨a, t, v, -⟩ := IsCofilteredOrEmpty.cone_objs b b'
  rw [← supportCommonRefinementIso_refine l E S M hM r s t,
    ← supportCommonRefinementIso_refine l E S M hM r' s' v]
  unfold supportCommonRefinementIso
  rw [supportRefinementIso_parallel l E S M hM (t.comp r) (v.comp r'),
    supportRefinementIso_parallel l E S M hM (t.comp s) (v.comp s')]

private theorem common_scalar_square
    {C D H : Type*} [Category C] [Category D] [Category H]
    (T : C ⥤ H) (U : D ⥤ H)
    {b c d : C} {b' c' d' : D} (r : b ≅ c) (s : b ≅ d)
    (r' : b' ≅ c') (s' : b' ≅ d')
    (qb : T.obj b ⟶ U.obj b') (qc : T.obj c ⟶ U.obj c')
    (qd : T.obj d ⟶ U.obj d')
    (hr : qb ≫ U.map r'.hom = T.map r.hom ≫ qc)
    (hs : qb ≫ U.map s'.hom = T.map s.hom ≫ qd) :
    qc ≫ U.map (r'.inv ≫ s'.hom) = T.map (r.inv ≫ s.hom) ≫ qd := by
  apply (cancel_epi (T.map r.hom)).1
  calc
    T.map r.hom ≫ (qc ≫ U.map (r'.inv ≫ s'.hom)) =
        qb ≫ U.map r'.hom ≫ U.map (r'.inv ≫ s'.hom) := by
      rw [← Category.assoc, ← hr, Category.assoc]
    _ = qb ≫ U.map s'.hom := by
      rw [← U.map_comp, Iso.hom_inv_id_assoc]
    _ = T.map s.hom ≫ qd := hs
    _ = T.map r.hom ≫ (T.map (r.inv ≫ s.hom) ≫ qd) := by
      rw [← Category.assoc, ← T.map_comp, Iso.hom_inv_id_assoc]

/-- The canonical refinement of integral support, in its constant-coefficient coordinates.
This is total limit of rho, conjugated by the universal native-limit restriction maps.
Source: Stacks 0941; auxiliary Steps 10--11
(blueprint: lem-pur-compact-support-strict-scalar-refinement). -/
def supportRefinementIntegral {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M)))) :
    (scalarConstantRestriction l E Y).obj ((scalarSupport l E c S).obj M) ≅
      (scalarConstantRestriction l E Y).obj ((scalarSupport l E d S).obj M) :=
  (scalarSupportLimit l E c S).app M ≪≫
    (scalarLimit l E Y).mapIso (supportRefinementIso l E r S M hM) ≪≫
    ((scalarSupportLimit l E d S).app M).symm

/-- The scalar comparison on integral support in constant/completed coordinates.
Its middle factor is exactly r_e^-1 Rlim(q) tau. The canonical scalarCompletion
identifies its source with restriction of completed scalar extension; no arbitrary
integral comparison is supplied. Source: Stacks 0941; auxiliary Steps 10--11
(blueprint: lem-pur-compact-support-strict-scalar-refinement). -/
def scalarIntegralRefinementComparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (baseTensor l E F i Y).obj
        ((scalarConstantRestriction l E Y).obj ((scalarSupport l E c S).obj M)) ⟶
      (scalarConstantRestriction l F Y).obj ((scalarSupport l F c S').obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) :=
  (baseTensor l E F i Y).map ((scalarSupportLimit l E c S).hom.app M) ≫
    scalarLimitArrow l E F i c S S' e he hepos M ≫
    (scalarSupportLimit l F c S').inv.app
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)

private theorem supportRefinementIntegral_hom {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M)))) :
    (supportRefinementIntegral l E r S M hM).hom =
      (scalarSupportLimit l E c S).hom.app M ≫
        (scalarLimit l E Y).map (supportRefinementIso l E r S M hM).hom ≫
        (scalarSupportLimit l E d S).inv.app M := by
  rfl

private theorem scalarIntegralRefinementComparison_eq {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    scalarIntegralRefinementComparison l E F i c S S' e he hepos M =
      (baseTensor l E F i Y).map ((scalarSupportLimit l E c S).hom.app M) ≫
        scalarLimitArrow l E F i c S S' e he hepos M ≫
        (scalarSupportLimit l F c S').inv.app
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) := by
  rfl

attribute [local irreducible] scalarSupportLimit scalarLimitArrow arrow
  supportCommonRefinementIso supportRefinementIntegral scalarIntegralRefinementComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_rComp_named {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (M : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (T l E F i Z).map
        (((rComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f g).hom ≫
          (eqToIso (congrArg
            (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) h)).hom).app M) ≫
        (proper l E F i k).app M =
      (proper l E F i g).app
          ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) f).obj M) ≫
        (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g).map
          ((proper l E F i f).app M) ≫
        (((rComp (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) f g).hom ≫
          (eqToIso (congrArg
            (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F))) h)).hom).app
            ((T l E F i X).obj M)) := by
  subst k
  simpa only [eqToIso_refl, Iso.refl_hom, NatTrans.comp_app,
    NatTrans.id_app, Category.comp_id] using strictScalarProperComposition l E F i f g M

section
attribute [local irreducible] compositionD gamma jComp rComp proper openTensor strictScalarPull

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Proper/open composition has the same scalar square, with the prescribed compositors.
Source: Stacks 0F7C--0F7D; auxiliary Step 9
(blueprint: lem-pur-compact-support-strict-scalar-refinement).
Proof: apply scalar_properOpen_gamma to the central square of the compatible tower.
Whisker by its outer proper/open operations. Proper mate pasting identifies the
proper scalar composite and open composition preserves summands. The resulting
map is compositionD, which uses exactly these compositors, on both sides. -/
theorem scalar_compactification_composition {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (c : Compactification.Triangle f g)
    [QuasiCompact c.cf.i] [QuasiCompact c.cg.i] [QuasiCompact c.q]
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (T l E F i Z).map
        ((compositionD (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) c).app N) ≫
        (comparison l E F i c.cfg).app N =
      (comparison l E F i c.cg).app ((image l E c.cf).obj N) ≫
        (image l F c.cg).map ((comparison l E F i c.cf).app N) ≫
        (compositionD (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) c).app
          ((T l E F i X).obj N) := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)
  have h := scalar_composition_pasting
    (T l E F i X) (T l E F i c.cf.Z) (T l E F i Y)
    (T l E F i c.cfg.Z) (T l E F i c.cg.Z) (T l E F i Z)
    (J A c.cf.i) (R A c.cf.g) (J A c.cg.i) (R A c.cg.g)
    (J A c.q) (R A c.p) (J A c.cfg.i) (R A c.cfg.g)
    (J B c.cf.i) (R B c.cf.g) (J B c.cg.i) (R B c.cg.g)
    (J B c.q) (R B c.p) (J B c.cfg.i) (R B c.cfg.g)
    (openTensor l E F i c.cf.i) (proper l E F i c.cf.g)
    (openTensor l E F i c.cg.i) (proper l E F i c.cg.g)
    (openTensor l E F i c.q) (proper l E F i c.p)
    (openTensor l E F i c.cfg.i) (proper l E F i c.cfg.g)
    (gamma A c.q c.cf.g c.p c.cg.i c.isPullback.w.symm)
    (gamma B c.q c.cf.g c.p c.cg.i c.isPullback.w.symm)
    ((jComp A c.cf.i c.q).hom ≫ (jCongr A c.i_q).hom)
    ((jComp B c.cf.i c.q).hom ≫ (jCongr B c.i_q).hom)
    ((rComp A c.p c.cg.g).hom ≫ (eqToIso (congrArg (R A) c.p_g)).hom)
    ((rComp B c.p c.cg.g).hom ≫ (eqToIso (congrArg (R B) c.p_g)).hom)
    (by intro M; exact_congr_type (scalar_jComp_named l E F i c.cf.i c.q c.cfg.i c.i_q M))
    (by intro M; exact_congr_type (scalar_rComp_named l E F i c.p c.cg.g c.cfg.g c.p_g M))
    (by
      intro M
      exact_congr_type
        (scalar_properOpen_gamma l E F i c.q c.cf.g c.p c.cg.i c.isPullback.w.symm M)) N
  simp only [compositionD, comparison, image, compositionF, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.comp_obj, Functor.map_comp, Category.assoc] at h ⊢
  exact_congr_type h

end

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem supportRefinement_app
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (supportRefinement l E r S).app M =
      (supportModel l E d S).hom.app M ≫
        (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).app
          ((reduction l E X S).obj M) ≫ (supportModel l E c S).inv.app M := by
  exact conjugate_whisker_app (reduction l E X S)
    (supportModel l E d S) (supportModel l E c S)
    (refinementComparison (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r)
    (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r)
    (comparison_eq _ r) (supportRefinement l E r S) (supportRefinement_eq l E r S) M

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem arrow_app
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (arrow l E F i c S S' e he hepos).app M =
      (T l E F i Y).map ((supportModel l E c S).hom.app M) ≫
        (comparison l E F i c).app ((reduction l E X S).obj M) ≫
        (image l F c).map ((reductionBalancing l E F i X S S' e he hepos).hom.app M) ≫
        (reindexImage l F c e hepos).inv.app
          ((reduction l F X S').obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ≫
        (subsequence l F Y e).map ((supportModel l F c S').inv.app
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) := by
  unfold arrow
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem supportRefinement_scalar
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (T l E F i Y).map ((supportRefinement l E r S).app M) ≫
        (arrow l E F i c S S' e he hepos).app M =
      (arrow l E F i d S S' e he hepos).app M ≫ (subsequence l F Y e).map
        ((supportRefinement l F r S').app
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  let : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  let NE := (reduction l E X S).obj M
  let NF := (reduction l F X S').obj
    ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
  have_cast_args ht := transport_square_of_eq (T l E F i Y) (subsequence l F Y e)
    (image l F d) (image l F c) (subsequence l F X e)
    ((supportModel l E c S).app M) ((supportModel l E d S).app M)
    ((supportModel l F c S').app
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
    ((supportModel l F d S').app
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
    ((compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) r).app NE)
    (compositionC (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) r)
    ((reductionBalancing l E F i X S S' e he hepos).hom.app M)
    ((comparison l E F i c).app NE) ((comparison l E F i d).app NE)
    ((reindexImage l F c e hepos).app NF) ((reindexImage l F d e hepos).app NF)
    ((supportRefinement l E r S).app M)
    ((supportRefinement l F r S').app
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
    ((arrow l E F i c S S' e he hepos).app M)
    ((arrow l E F i d S S' e he hepos).app M)
    (supportRefinement_app l E r S M)
    (supportRefinement_app l F r S'
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))
    (arrow_app l E F i c S S' e he hepos M)
    (arrow_app l E F i d S S' e he hepos M)
    (refinement_scalar_comparison l E F i r NE)
    (refinement_reindex l E F i r e hepos NF)
  exact_congr_type ht

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalarLimitArrow_eq
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    [IsIso (scalarLimitRestriction l F Y e)]
    (M : DerivedCategory (scalarReductionSource l E X)) :
    scalarLimitArrow l E F i c S S' e he hepos M =
      (scalarLimitTensor l E F i Y).hom.app ((support l E c S).obj M) ≫
        (scalarLimit l F Y).map ((arrow l E F i c S S' e he hepos).app M) ≫
        inv ((scalarLimitRestriction l F Y e).app ((support l F c S').obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M))) := by
  unfold scalarLimitArrow scalarLimitCofinalInverse
  rfl

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- The actual constant reductions have separate bounded-below finite-etale-origin witnesses.
Source: constructible origin and finite-free coefficient models; auxiliary Step 1
(blueprint: lem-pur-compact-support-strict-scalar-refinement).
Proof: finite-free extension preserves derived completeness, constructibility and the
uniform reduction Tor interval. Each reduction of M and of its scalar extension is
bounded constructible. Apply constructible_proEtale_origin at that finite coefficient
ring, then its restriction to the discrete integral ring. The support-model evaluation
identifies this with evaluation of reduction. Choose the witness independently for
each n; no single lower bound is asserted or needed. -/
theorem scalar_refinement_origins (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    (∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M)))) ∧
    ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X n).obj
        ((reduction l F X S').obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)))) := by
  let _ := c
  exact ⟨scalar_refinement_origins_E l E D hl f S M _hM,
    scalar_refinement_origins_F l E F i D hl f S' M _hM⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The scalar mate commutes with the actual normalized refinement, before evaluation.
The second equation is its total-limit square with the prescribed tau and cofinal map.
Source: Stacks 0F7B--0F7D; auxiliary comparison Steps 1--10
(blueprint: lem-pur-compact-support-strict-scalar-refinement).
Proof:
1. Use scalar_refinement_origins for the E and F reduction towers. Open immersions
in both compactifications are quasi-compact since f is quasi-compact and the proper
maps are quasi-separated. The strict proper/open calculus therefore applies.
2. Apply strictRefinementRestrictionSquares to the normalized compositionC maps.
Its first face commutes with pastedRestriction; comparison_pasted identifies the
scalar comparison as its inverse mate. Naturality of inverse mates, proved from
the scalar adjunction units, gives the scalar square for compositionC.
3. Invert the arithmetic-selection face, paste with naturality of the ramified
input balancing, and conjugate by the prescribed supportModel isomorphisms.
Cancel adjacent model maps. This gives the square for supportRefinement on the
native strict towers, including all quotient transitions.
4. Invert Theta inside the derived strict B-tower category using
supportRefinement_isIso. This gives exactly rho_F^(e) q_c = q_d T(rho_E).
No evaluation functor is assumed faithful.
5. Naturality of scalarLimitTensor and scalarLimitRestriction transports this square
to scalarLimitArrow = r_e^-1 Rlim(q) tau. The published scalarRoosNormalization and
scalarRoosTensorNormalization identify these factors with their selection/block and
product coordinates and preserve every strict augmentation (0,a). The canonical
scalarSupportLimit and scalarCompletion transports give the completed support square. -/
theorem compactSupportStrictScalarRefinement {c d : Compactification f}
    (r : c.Refinement d) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    ((arrow l E F i c S S' e he hepos).app M ≫
        (subsequence l F Y e).map
          (supportRefinementIso l F r S'
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
            (scalar_refinement_origins l E F i D hl f c S S' M hM).2).hom =
      (T l E F i Y).map
          (supportRefinementIso l E r S M
            (scalar_refinement_origins l E F i D hl f c S S' M hM).1).hom ≫
        (arrow l E F i d S S' e he hepos).app M) ∧
    (scalarLimitArrow l E F i c S S' e he hepos M ≫
        (scalarLimit l F Y).map
          (supportRefinementIso l F r S'
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
            (scalar_refinement_origins l E F i D hl f c S S' M hM).2).hom =
      (baseTensor l E F i Y).map
          ((scalarLimit l E Y).map
            (supportRefinementIso l E r S M
              (scalar_refinement_origins l E F i D hl f c S S' M hM).1).hom) ≫
        scalarLimitArrow l E F i d S S' e he hepos M) := by
  let hE := (scalar_refinement_origins l E F i D hl f c S S' M hM).1
  let hF := (scalar_refinement_origins l E F i D hl f c S S' M hM).2
  let MF := (pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M
  have hs : (arrow l E F i c S S' e he hepos).app M ≫
      (subsequence l F Y e).map (supportRefinementIso l F r S' MF hF).hom =
      (T l E F i Y).map (supportRefinementIso l E r S M hE).hom ≫
        (arrow l E F i d S S' e he hepos).app M := by
    have_cast_args h := inverse_square_of_eq (T l E F i Y) (subsequence l F Y e)
      (supportRefinementIso l E r S M hE) (supportRefinementIso l F r S' MF hF)
      ((supportRefinement l E r S).app M) ((supportRefinement l F r S').app MF)
      (supportRefinementIso_inv l E r S M hE)
      (supportRefinementIso_inv l F r S' MF hF)
      ((arrow l E F i c S S' e he hepos).app M)
      ((arrow l E F i d S S' e he hepos).app M)
      (supportRefinement_scalar l E F i r S S' e he hepos M)
    exact_congr_type h
  refine ⟨hs, ?_⟩
  let := scalarLimitRestriction_isIso l F Y e hepos
  exact limit_square_of_eq (T l E F i Y) (subsequence l F Y e)
    (scalarLimit l E Y) (scalarLimit l F Y) (scalarLimit l F Y)
    (baseTensor l E F i Y) (scalarLimitTensor l E F i Y).hom
    (scalarLimitRestriction l F Y e)
    (supportRefinementIso l E r S M hE).hom
    (supportRefinementIso l F r S' MF hF).hom
    ((arrow l E F i c S S' e he hepos).app M)
    ((arrow l E F i d S S' e he hepos).app M)
    (scalarLimitArrow l E F i c S S' e he hepos M)
    (scalarLimitArrow l E F i d S S' e he hepos M)
    (scalarLimitArrow_eq l E F i c S S' e he hepos M)
    (scalarLimitArrow_eq l E F i d S S' e he hepos M) hs

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Common-refinement squares and the canonical integral support square.
Source: Stacks 0F7C--0F7D, 0941; auxiliary Steps 9--11
(blueprint: lem-pur-compact-support-strict-scalar-refinement).
Proof: apply compactSupportStrictScalarRefinement to both arrows of the common
refinement and invert/paste their squares. This gives the first assertion.
For independence, dominate two common refinements and equalize their parallel
arrows using prop-compactification-refinement. The composition equation of
supportRefinementIso_coherence cancels the extra invertible comparisons, giving
independence of all choices. For three compactifications pass to one common
refinement and cancel its middle comparison to get the cocycle.
Finally conjugate the total-limit square by scalarSupportLimit. This is the
integral definition's comparison, since its maps are total limits of the same
finite proper/open comparisons. The Roos normalization preserves the projections
and all augmentations, not just objects. scalarCompletion is normalized on pure
tensors and on whole-complex counits; the constant/completed equivalence therefore
transports precisely this square to completed integral compact support. -/
theorem compactSupportStrictScalarRefinementCoherence
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (c₀ : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    (∀ (c d b : Compactification f) (r : b.Refinement c) (s : b.Refinement d),
      (arrow l E F i c S S' e he hepos).app M ≫
          (subsequence l F Y e).map
            (supportCommonRefinementIso l F r s S'
              ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
              (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).2).hom =
        (T l E F i Y).map
            (supportCommonRefinementIso l E r s S M
              (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).1).hom ≫
          (arrow l E F i d S S' e he hepos).app M) ∧
    (∀ (c d b b' : Compactification f) (r : b.Refinement c) (s : b.Refinement d)
      (r' : b'.Refinement c) (s' : b'.Refinement d),
      supportCommonRefinementIso l E r s S M
          (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).1 =
        supportCommonRefinementIso l E r' s' S M
          (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).1) ∧
    (∀ (c d a b b' b'' : Compactification f)
      (r : b.Refinement c) (s : b.Refinement d)
      (s' : b'.Refinement d) (t : b'.Refinement a)
      (r' : b''.Refinement c) (t' : b''.Refinement a),
      supportCommonRefinementIso l E r s S M
          (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).1 ≪≫
          supportCommonRefinementIso l E s' t S M
            (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).1 =
        supportCommonRefinementIso l E r' t' S M
          (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).1) ∧
    ∀ (c d : Compactification f) (r : c.Refinement d),
      scalarIntegralRefinementComparison l E F i c S S' e he hepos M ≫
          (supportRefinementIntegral l F r S'
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
            (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).2).hom =
        (baseTensor l E F i Y).map
            (supportRefinementIntegral l E r S M
              (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).1).hom ≫
          scalarIntegralRefinementComparison l E F i d S S' e he hepos M := by
  let hE := (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).1
  let hF := (scalar_refinement_origins l E F i D hl f c₀ S S' M hM).2
  let MF := (pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c d b r s
    have hs := common_scalar_square (T l E F i Y) (subsequence l F Y e)
        (supportRefinementIso l E r S M hE) (supportRefinementIso l E s S M hE)
        (supportRefinementIso l F r S' MF hF) (supportRefinementIso l F s S' MF hF)
        ((arrow l E F i b S S' e he hepos).app M)
        ((arrow l E F i c S S' e he hepos).app M)
        ((arrow l E F i d S S' e he hepos).app M)
        (compactSupportStrictScalarRefinement l E F i D hl f r S S' e he hepos M hM).1
        (compactSupportStrictScalarRefinement l E F i D hl f s S S' e he hepos M hM).1
    rw [supportCommonRefinementIso_hom, supportCommonRefinementIso_hom]
    exact hs
  · intro c d b b' r s r' s'
    exact supportCommonRefinementIso_independent l E S M hE r s r' s'
  · intro c d a b b' b'' r s s' t r' t'
    obtain ⟨z, v, w, -⟩ := IsCofilteredOrEmpty.cone_objs b b'
    rw [← supportCommonRefinementIso_refine l E S M hE r s v,
      supportCommonRefinementIso_independent l E S M hE s' t (v.comp s) (w.comp t),
      supportCommonRefinementIso_independent l E S M hE r' t' (v.comp r) (w.comp t)]
    apply Iso.ext
    simp only [supportCommonRefinementIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
  · intro c d r
    have h := (compactSupportStrictScalarRefinement
      l E F i D hl f r S S' e he hepos M hM).2
    have hb : (baseTensor l E F i Y).map ((scalarSupportLimit l E d S).inv.app M) ≫
        (baseTensor l E F i Y).map ((scalarSupportLimit l E d S).hom.app M) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app]
      exact (baseTensor l E F i Y).map_id _
    rw [scalarIntegralRefinementComparison_eq, scalarIntegralRefinementComparison_eq,
      supportRefinementIntegral_hom, supportRefinementIntegral_hom]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [reassoc_of% hb, reassoc_of% h]

end Geometry
end WeilConjectures.PurStrictScalar
