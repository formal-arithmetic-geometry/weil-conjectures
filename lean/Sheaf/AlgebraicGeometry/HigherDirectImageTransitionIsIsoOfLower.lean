/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients

/-! # Isomorphisms of higher-image transitions

Source: Stacks Project Tag 09Z1.
(blueprint: lem-sbc-higher-image-transition-isIso-of-lower)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lowerStarPlusTransition

variable (Λ : Type (u + 1)) [CommRing Λ]

-- Construct this standard theorem application explicitly; Lean's kernel checks it.
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
        return ← congrProofs cache pairs n a' b'
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

elab "bc_structural_exact " n:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    structuralExact (← Lean.Meta.getLocalDeclFromUserName n.getId).toExpr

elab "bc_structural_rfl" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let type ← Lean.instantiateMVars (← goal.getType)
    let some (_, a, b) := type.eq? | throwError "expected equality"
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let h ← Lean.Meta.withTransparency .reducible (congrProofs cache #[] 300 a b)
    goal.assign (← toEq h)

-- Apply categorical pasting with explicitly computed objects and arrow conversions.
-- Every generated conversion is an equality proof checked by the kernel.
elab "bc_paste " d:ident " using " hu:ident hv:ident hn:ident hs:ident ho:ident : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let localExpr (n : Lean.Syntax) := do
      return (← Lean.Meta.getLocalDeclFromUserName n.getId).toExpr
    let hU ← localExpr hu
    let hV ← localExpr hv
    let hN ← localExpr hn
    let hS ← localExpr hs
    let sides (h : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
      let t ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← Lean.Meta.inferType h))
      let some (_, l, r) := t.consumeMData.eq? |
        throwError "expected equality in hypothesis: {t.getAppFn}"
      return (l, r)
    let split (e : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
      let xs := e.getAppArgs
      unless e.getAppFn.isConstOf ``CategoryTheory.CategoryStruct.comp do
        throwError "expected composition"
      return (xs[xs.size - 2]!, xs.back!)
    let (cU, rhsU) ← sides hU
    let (iU, restU) ← split rhsU
    let (u₁, u₂) ← split restU
    let (cV, rhsV) ← sides hV
    let (iV, restV) ← split rhsV
    let (v₁, v₂) ← split restV
    let (lhsN, rhsN) ← sides hN
    let (r₁, tailN) ← split lhsN
    let (r₂, _) ← split tailN
    let (_, tailN') ← split rhsN
    let (t₁, t₂) ← split tailN'
    let (_, rhsS) ← sides hS
    let (_, tailS) ← split rhsS
    let (s₁, s₂) ← split tailS
    let target ← Lean.Meta.zetaReduce (← Lean.instantiateMVars (← goal.getType))
    let some (_, _, rhsGoal) := target.consumeMData.eq? |
      throwError "expected equality in goal: {target.getAppFn}"
    let (_, s) ← split rhsGoal
    let endpoints (f : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
      let xs := (← Lean.instantiateMVars (← Lean.Meta.inferType f)).getAppArgs
      return (xs[xs.size - 2]!, xs.back!)
    let (A, B) ← endpoints r₁
    let (_, D) ← endpoints r₂
    let (_, E) ← endpoints iU
    let (_, F) ← endpoints iV
    let (_, G) ← endpoints t₁
    let (_, H) ← endpoints u₁
    let (_, I) ← endpoints u₂
    let (_, J) ← endpoints v₁
    let (_, K) ← endpoints v₂
    let (_, L) ← endpoints s₁
    let C ← Lean.Meta.inferType A
    let some clevel := (← Lean.Meta.getLevel C).dec |
      throwError "expected a category object type in Type"
    let ftype ← Lean.instantiateMVars (← Lean.Meta.inferType r₁)
    let hlevel := ftype.getAppFn.constLevels![0]!
    let catType := Lean.mkApp (Lean.mkConst ``CategoryTheory.Category [hlevel, clevel]) C
    let cat ← Lean.Meta.synthInstance catType
    let ho ← localExpr ho
    let args := #[C, cat, A, B, D, E, F, G, H, I, J, K, L,
      r₁, r₂, iU, iV, t₁, t₂, u₁, u₂, v₁, v₂, s₁, s₂, cU, cV, s,
      hU, hV, hN, hS, ho]
    let declName ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo d
    let info ← Lean.getConstInfo declName
    let .forallE _ (.sort (.succ (.param objectLevel))) _ _ := info.type |
      throwError "expected the object type as the first parameter"
    let levels := info.levelParams.map fun n =>
      if n == objectLevel then clevel else hlevel
    goal.assign (Lean.mkAppN (Lean.mkConst declName levels) args)

private lemma map_comp_isIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (G : C ⥤ D) (H : D ⥤ E) {X : D} {Y Z : C}
    (f : X ⟶ G.obj Y) (g : Y ⟶ Z) [IsIso f] [IsIso g] :
    IsIso (H.map (f ≫ G.map g)) := by infer_instance

/-- A higher-image transition is invertible whenever its derived triangle transition is.

Source: Stacks Project Tag 09Z1, canonical restriction maps.
(blueprint: lem-sbc-higher-image-transition-isIso-of-lower)

Proof: The higher-image transition is homology of the derived triangle transition
followed by derived direct image of the exact pullback-single comparison. The latter
is an isomorphism. Composition and functors preserve isomorphisms. -/
lemma higherDirectImageTransition_isIso_of_lower
    {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X)
    (w : a ≫ h = h') (q : ℤ)
    (C : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (ht : IsIso (lowerStarPlusTransition Λ a h h' w
      ((DerivedCategory.Plus.singleFunctor _ 0).obj C))) :
    IsIso (higherDirectImageTransition Λ a h h' w q C) := by
  have : IsIso (lowerStarPlusTransition Λ a h h' w
      ((DerivedCategory.Plus.singleFunctor _ 0).obj C)) := ht
  have hm := map_comp_isIso R+((h')_*[ModuleCat.{u + 1} Λ])
    (DerivedCategory.Plus.homologyFunctor _ q)
    (lowerStarPlusTransition Λ a h h' w _)
    ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app C)
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let p := (← Lean.Meta.getLocalDeclFromUserName `hm).toExpr
      structuralExact p

/-- Map a coefficient morphism through higher direct image with explicit endpoint objects.
Source: Stacks Tag 09Z1, functoriality of the higher direct image.
(blueprint: lem-sbc-higher-image-transition-isIso-of-lower) -/
noncomputable def higherDirectImageMap {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') :
    higherDirectImage Λ h q F ⟶ higherDirectImage Λ h q F' :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    (R+((h)_*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map f))

/-- The mapping API is the nested single-complex, direct-image and homology map.
Source: Stacks Tag 09Z1, functoriality of higher direct images.
(blueprint: lem-sbc-higher-image-transition-isIso-of-lower) -/
lemma higherDirectImageMap_eq {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') :
    higherDirectImageMap Λ h q f =
      (DerivedCategory.Plus.homologyFunctor _ q).map
        (R+((h)_*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map f)) := by
  rfl

/-- Restriction over a fixed base uses the higher-image mapping API.
Source: Stacks Tag 09Z1, canonical restriction maps.
(blueprint: lem-sbc-higher-image-transition-isIso-of-lower) -/
lemma higherDirectImageOverMap_eq {W X : Scheme.{u}} (k : W ⟶ X)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {U V : Over W} (φ : U ⟶ V) :
    higherDirectImageOverMap Λ k G q φ =
      higherDirectImageTransition Λ φ.left (V.hom ≫ k) (U.hom ≫ k)
        (by rw [← Category.assoc, Over.w]) q _ ≫
      higherDirectImageMap Λ (U.hom ≫ k) q
        ((upperStarComp (ModuleCat.{u + 1} Λ) φ.left V.hom U.hom
          (Over.w φ).symm).inv.app G) := by
  rfl

/-- The usual target functor comparison, with its codomain written as higherDirectImage.

This is the existing canonical isomorphism with functor-object parentheses made explicit.
(blueprint: lem-sbc-higher-image-transition-isIso-of-lower) -/
noncomputable def baseChangeTargetFunctorHigherImageIso
    {X T Y : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (baseChangeTargetFunctor Λ e h q).obj F ≅
      higherDirectImage Λ h q (((e)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  (DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).mapIso
    (R+((h)_*[ModuleCat.{u + 1} Λ]).mapIso
      ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F))

/-- Map a coefficient isomorphism through higher direct image, with explicit object types.
(blueprint: lem-sbc-higher-image-transition-isIso-of-lower) -/
noncomputable def higherDirectImageMapIso {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ≅ F') :
    higherDirectImage Λ h q F ≅ higherDirectImage Λ h q F' :=
  (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (R+((h)_*[ModuleCat.{u + 1} Λ]).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso f))

/-- The coefficient-isomorphism API uses the same mapped coefficient morphism.
Source: Stacks Tag 09Z1, functoriality of higher direct images.
(blueprint: lem-sbc-higher-image-transition-isIso-of-lower) -/
lemma higherDirectImageMapIso_hom_eq {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ≅ F') :
    (higherDirectImageMapIso Λ h q f).hom = higherDirectImageMap Λ h q f.hom := by
  rfl


end AlgebraicGeometry.Etale
