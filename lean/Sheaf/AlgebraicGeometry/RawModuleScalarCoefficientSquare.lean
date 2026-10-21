/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientFactors
public import Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted

/-! # Coefficient factors of the derived scalar pullback square

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] RawModuleScalarComparison.derivedPullbackIso

/-- The shifted coefficient part of scalar comparison.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: lem-sbc-raw-scalar-coefficient-square). -/
noncomputable def scalarCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W Y : Scheme.{u}} (h : Y ⟶ W)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj
          ((RawModuleScalarComparison.forget Λ W).obj G)))⟦q⟧ :=
  ((RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h).obj G)) ≫
    (shiftFunctor _ q).map
      (((RawModuleScalarComparison.forget Λ Y).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj G) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ h G)))

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

private theorem shift_square
    {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    [HasShift C₀ ℤ] [HasShift C₁ ℤ] [HasShift D₀ ℤ] [HasShift D₁ ℤ]
    (M : C₀ ⥤ C₁) (VA : C₁ ⥤ D₁) (VB : C₀ ⥤ D₀) (H : D₀ ⥤ D₁)
    [M.CommShift ℤ] [VA.CommShift ℤ] [VB.CommShift ℤ] [H.CommShift ℤ]
    (e : VB ⋙ H ⟶ M ⋙ VA) [NatTrans.CommShift e ℤ]
    (X : C₀) (Y : C₁) (Z : D₀) (T : D₁)
    (m : M.obj X ⟶ Y) (bA : VA.obj Y ⟶ T) (bB : VB.obj X ⟶ Z) (a : H.obj Z ⟶ T)
    (hu : e.app X ≫ VA.map m ≫ bA = H.map bB ≫ a) (q : ℤ) :
    e.app (X⟦q⟧) ≫
      VA.map ((M.commShiftIso q).hom.app X ≫ m⟦q⟧') ≫
      (VA.commShiftIso q).hom.app Y ≫ bA⟦q⟧' =
    H.map ((VB.commShiftIso q).hom.app X ≫ bB⟦q⟧') ≫
      (H.commShiftIso q).hom.app Z ≫ a⟦q⟧' := by
  have hc := NatTrans.shift_app_comm e q X
  simp only [Functor.commShiftIso_comp_hom_app] at hc
  simp only [Functor.map_comp, Category.assoc]
  rw [VA.commShiftIso_hom_naturality_assoc]
  rw [← reassoc_of% hc]
  rw [H.commShiftIso_hom_naturality_assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ H.map ((VB.commShiftIso q).hom.app X) ≫
      (H.commShiftIso q).hom.app (VB.obj X) ≫ t⟦q⟧') hu

/-- Shift transport from the unshifted coefficient square.
Source: Stacks Project, Tags 03D7 and 03Q8. The proof applies the generic
shift transport identity to the four derived functors and the unshifted
coefficient identity `coefficient_unshifted`. The required commutation of
the comparison maps with shifts follows from `NatTrans.shift_app_comm` and
the naturality of each `commShiftIso`; functoriality of shifts and
associativity then produce the displayed equality. This applies to every
integer shift, including zero and negative shifts, and to identity arrows
and zero coefficient sheaves.
(blueprint: lem-sbc-raw-scalar-coefficient-square-shift-transport). -/
theorem rawModuleScalar_coefficient_square_of_unshifted
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B)
    : 
  let VA := (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus
  let FB := (upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G
  let bA := scalarCoefficientFactor Λ A.hom G q
  let bB := scalarCoefficientFactor Λ B.hom G q
  let mT := moduleCoefficientFactor Λ G q A B f
  let aT := abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G) q A B f
  (RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
      (((DerivedCategory.Plus.singleFunctor _ 0).obj FB)⟦q⟧) ≫
    VA.map mT ≫ bA = H.map bB ≫ aT := by
  have := rawModuleScalar_derivedPullbackIso_commShift Λ f.left
  let M := (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus
  let VA := (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus
  let VB := (RawModuleScalarComparison.forget Λ B.left).mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus
  let e := (RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv
  let X := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G)
  let Y := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G)
  let Z := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} B.hom).obj
      ((RawModuleScalarComparison.forget Λ W).obj G))
  let T := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} A.hom).obj
      ((RawModuleScalarComparison.forget Λ W).obj G))
  let m : M.obj X ⟶ Y :=
    ((upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
          (Over.w f).symm).inv.app G)
  let bA : VA.obj Y ⟶ T :=
    ((RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (inv (RawModuleScalarComparison.pullback Λ A.hom G))
  let bB : VB.obj X ⟶ Z :=
    ((RawModuleScalarComparison.forget Λ B.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (inv (RawModuleScalarComparison.pullback Λ B.hom G))
  let a : H.obj Z ⟶ T :=
    ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
          (Over.w f).symm).inv.app _)
  have hu := rawModuleScalar_coefficient_unshifted Λ G A B f
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let mut inputs := #[]
      for name in [`M, `VA, `VB, `H, `e, `X, `Y, `Z, `T, `m, `bA, `bB, `a, `hu, `q] do
        inputs := inputs.push (← Lean.Meta.getLocalDeclFromUserName name).toExpr
      let proof ← Lean.Meta.mkAppM ``shift_square (inputs.extract 0 13)
      let proof ← Lean.instantiateMVars
        (Lean.mkAppN proof (inputs.extract 13 15))
      let mut pairs := #[]
      let ring ← Lean.Meta.getLocalDeclFromUserName `Λ
      let sheaf ← Lean.Meta.getLocalDeclFromUserName `G
      for name in [`A, `B] do
        let object ← Lean.Meta.getLocalDeclFromUserName name
        let equation ← Lean.Meta.mkAppM ``higherDirectImageRawOverComplex_eq
          #[ring.toExpr, sheaf.toExpr, object.toExpr]
        let some (_, lhs, rhs) := (← Lean.Meta.inferType equation).eq?
          | throwError "expected coefficient complex equation"
        let equation ← Lean.Meta.mkAppM ``heq_of_eq #[equation]
        pairs := pairs.push (lhs, rhs, equation)
      let target := (← Lean.Meta.whnf (← goal.getType)).consumeMData
      let some (_, lhs, rhs) := target.eq? | throwError "expected equality"
      let proofType ← Lean.Meta.transform
        (← Lean.instantiateMVars (← Lean.Meta.inferType proof)) (pre := fun e => do
          if let .fvar id := e then
            if let some value ← id.getValue? then return .visit value
          return .continue)
      let proofType ← Lean.Meta.whnf proofType
      let some (_, lhs', rhs') := proofType.consumeMData.eq?
        | throwError "expected equality proof"
      let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
      let hl ← Lean.Meta.withTransparency .reducible (rawScalarCongrProofs cache pairs 200 lhs lhs')
      let hr ← Lean.Meta.withTransparency .reducible (rawScalarCongrProofs cache pairs 200 rhs' rhs)
      let hm ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
      let hh ← Lean.Meta.mkHEqTrans hl hm
      let hh ← Lean.Meta.mkHEqTrans hh hr
      goal.assign (← scalarToEq hh)

theorem rawModuleScalar_coefficient_square
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
  let VA := (RawModuleScalarComparison.forget Λ A.left).mapDerivedCategoryPlus
  let H := (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus
  let FB := (upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G
  let bA := scalarCoefficientFactor Λ A.hom G q
  let bB := scalarCoefficientFactor Λ B.hom G q
  let mT := moduleCoefficientFactor Λ G q A B f
  let aT := abelianCoefficientFactor ((RawModuleScalarComparison.forget Λ W).obj G) q A B f
  (RawModuleScalarComparison.derivedPullbackIso Λ f.left).inv.app
      (((DerivedCategory.Plus.singleFunctor _ 0).obj FB)⟦q⟧) ≫
    VA.map mT ≫ bA = H.map bB ≫ aT := by
  exact rawModuleScalar_coefficient_square_of_unshifted Λ G q A B f

end AlgebraicGeometry.Etale
