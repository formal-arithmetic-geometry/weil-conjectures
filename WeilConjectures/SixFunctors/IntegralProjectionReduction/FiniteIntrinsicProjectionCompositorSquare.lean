/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionCoordinates.FiniteIntrinsicProjectionOpenCoordinates
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FinitePullbackCompositionFixedCoordinates
import Mathlib.Lean.Meta.CongrTheorems
import Mathlib.Logic.Function.Basic

/-! # Open comparison for the specified finite tensor realization

Source: fix-prop-projection-formula.proof.md, same projection map; Stacks 0B56, 0E8I.
(blueprint: lem-sf-finite-intrinsic-projection-compositor-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction
open CompactSupportFiniteProjection FiniteIntrinsicProjectionCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

attribute [local implicit_reducible] sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory
  realization sixFunctorFiniteRealization sixFunctorFinitePullback coordinates
  fixedTensor fixedDerivedPull finiteTorConstructible
  integralCoefficientSheaf integralCoefficientCommRingSheaf sixFunctorFiniteSupport
  tensor partialTensor torPull sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor sfIntrinsicModuleEquivalence AlgebraicGeometry.ProEtale.derivedTensor
  sfIntrinsicCompactSupportComparison
  AlgebraicGeometry.ProEtale.leftDerivedUpperStarCompactificationIso

private theorem presentationNatTransCongr
    {C D : Type*} [Category C] [Category D]
    (F G F' G' : C ⥤ D) (hF : F = F') (hG : G = G') :
    NatTrans F G = NatTrans F' G' := by
  cases hF
  cases hG
  rfl

/- Factor conversion through small congruences. The resulting terms are checked by the
kernel; the coefficient equivalences and derived functors remain abstract. -/
open Lean Meta in
private meta def presentationStep : Nat → Expr → MetaM (Option Expr)
  | 0, _ => pure none
  | fuel + 1, e₀ => do
    let e := (← instantiateMVars e₀).consumeMData.headBeta
    if e != e₀ then return some e
    match e with
    | .letE _ _ v body _ => return some (body.instantiate1 v)
    | .fvar id => return (← id.getDecl).value? (allowNondep := true)
    | _ => pure ()
    let args := e.getAppArgs
    let fn := e.getAppFn
    let proj? : Option (Name × Nat × Expr × Option Nat) ← match fn with
      | .proj typeName index major => pure (some (typeName, index, major, none))
      | .const name _ => do
        if let some info ← getProjectionFnInfo? name then
          if args.size > info.numParams then
            let ci ← getConstInfoCtor info.ctorName
            pure (some (ci.induct, info.i, args[info.numParams]!, some info.numParams))
          else pure none
        else pure none
      | _ => pure none
    if let some (typeName, index, major, argIndex) := proj? then
      if let .const ctorName _ := major.getAppFn then
        if let .ctorInfo ci ← getConstInfo ctorName then
          if ci.induct == typeName then
            let value := major.getAppArgs[ci.numParams + index]!
            let tail := match argIndex with
              | none => args
              | some i => args.extract (i + 1) args.size
            return some ((mkAppN value tail).headBeta)
      if let some major' ← presentationStep fuel major then
        return some (match argIndex with
          | none => mkAppN (.proj typeName index major') args
          | some i => mkAppN fn (args.set! i major'))
      return none
    if let .const name us := fn then
      if #[``SystemProjectionFormula.finitePullComp, ``finiteDerivedPullback,
          ``finiteCoefficientRing, ``realization, ``sixFunctorFiniteRealization,
          ``FiniteIntrinsicProjectionCoordinates.beforeCompositor,
          ``FiniteIntrinsicProjectionCoordinates.fixedCompositorPart,
          ``CompactSupportFiniteProjection.fixedTensor, ``evaluatedTensor,
          ``CompactSupportFiniteProjection.tensor,
          ``sixFunctorFiniteSupport, ``sfIntrinsicCompactSupport, ``sfFixedCompactSupport,
          ``sfAmbientCompactSupportCandidate,
          ``AlgebraicGeometry.ProEtale.leftDerivedUpperStarCompactificationIso,
          ``Functor.comp, ``Functor.uncurry, ``Functor.postcompose₂,
          ``Functor.whiskeringLeft₂, ``Functor.whiskeringLeft, ``Functor.whiskeringRight,
          ``Iso.app, ``Iso.trans, ``Iso.symm, ``Functor.mapIso,
          ``NatTrans.vcomp, ``NatTrans.id, ``NatIso.ofComponents, ``Functor.category,
          ``ObjectProperty.ι, ``inducedFunctor].contains name then
        let ci ← getConstInfo name
        if let .defnInfo _ := ci then
          return some ((← instantiateValueLevelParams ci us).beta args)
    return none

open Lean Meta in
private meta def presentationHEq
    (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) :
    Nat → Expr → Expr → Array (Expr × Expr × Expr) → MetaM Expr
  | 0, a, b, _ => throwError "presentation depth exhausted: {a.getAppFn} / {b.getAppFn}"
  | fuel + 1, a₀, b₀, links => do
    let a := (← instantiateMVars a₀).consumeMData.headBeta
    let b := (← instantiateMVars b₀).consumeMData.headBeta
    let key := (a,b)
    if let some h := (← cache.get).get? key then return h
    let h ← do
      if a == b then return ← mkHEqRefl a
      for (x,y,h) in links do
        if a == x && b == y then return h
      if (← isProof a) && (← isProof b) then
        return ← mkAppM ``proof_irrel_heq #[a,b]
      let af₀ := a.getAppFn
      let bf₀ := b.getAppFn
      let sameConst := af₀.isConst && bf₀.isConst &&
        (af₀.constName?.getD `_) == (bf₀.constName?.getD `_)
      if sameConst && #[``ModuleCat, ``ModuleCat.moduleCategory,
          ``CategoryTheory.Sheaf, ``CategoryTheory.Presheaf.IsSheaf,
          ``CategoryTheory.sheafIsAbelian, ``ModuleCat.abelian,
          ``HasDerivedCategory.ofIsGrothendieckAbelian, ``instCategoryDerivedCategory,
          ``DerivedCategory, ``ObjectProperty.FullSubcategory.category, ``CategoryTheory.Functor,
          ``sfIntrinsicDerivedEquivalence, ``sfIntrinsicDerivedPullback,
          ``sfIntrinsicDerivedPullbackComp,
          ``sfFixedCompactSupport, ``sfAmbientCompactSupportCandidate].contains
            (af₀.constName?.getD `_) then
        if ← withTransparency .reducible (isDefEq a b) then
          return ← mkHEqRefl a
      let ta := (← inferType a).getAppFn
      if ta.isConst && #[``Ring, ``CommRing, ``Semiring, ``CommSemiring,
          ``Field, ``AddCommGroup, ``AddGroup, ``Monoid, ``CommMonoid].contains
            (ta.constName?.getD `_) then
        if ← isDefEq a b then return ← mkHEqRefl a
      if a.isLambda && b.isLambda then
        let hd ← mkEqOfHEq (← presentationHEq cache fuel
          a.bindingDomain! b.bindingDomain! links)
        return ← withLocalDeclD `x a.bindingDomain! fun x => do
          withLocalDeclD `y b.bindingDomain! fun y => do
            withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
              let hb ← presentationHEq cache fuel (mkApp a x).headBeta
                (mkApp b y).headBeta (links.push (x,y,hxy))
              let hf ← mkLambdaFVars #[x,y,hxy] hb
              let aTy ← whnf (← inferType a)
              let bTy ← whnf (← inferType b)
              let P := mkLambda aTy.bindingName! aTy.bindingInfo! aTy.bindingDomain!
                aTy.bindingBody!
              let Q := mkLambda bTy.bindingName! bTy.bindingInfo! bTy.bindingDomain!
                bTy.bindingBody!
              mkAppOptM ``Function.hfunext #[some a.bindingDomain!, some b.bindingDomain!,
                some P, some Q, some a, some b, some hd, some hf]
      let unfoldHead (e : Expr) : MetaM (Option Expr) := do
        match e with
        | .letE _ _ v body _ => return some (body.instantiate1 v)
        | .fvar id => return (← id.getDecl).value? (allowNondep := true)
        | _ =>
          if let .const n us := e.getAppFn then
            if (← getProjectionFnInfo? n).isSome then return none
            let ci ← getConstInfo n
            if let .defnInfo _ := ci then
              return some ((← instantiateValueLevelParams ci us).beta e.getAppArgs)
          return none
      let sameOrdinary ← if sameConst then
        pure (← getProjectionFnInfo? (af₀.constName?.getD `_)).isNone
        else pure false
      if !sameOrdinary then
        if let some a' ← presentationStep 40 a then
          return ← presentationHEq cache fuel a' b links
        if let some b' ← presentationStep 40 b then
          return ← presentationHEq cache fuel a b' links
      let expandProjection (e : Expr) : MetaM Expr := do
        let .proj typeName index major := e.getAppFn | return e
        let info := Lean.getStructureInfo (← getEnv) typeName
        let p ← mkProjection major info.fieldNames[index]!
        return mkAppN p e.getAppArgs
      let a' ← expandProjection a
      let b' ← expandProjection b
      if a' != a || b' != b then
        return ← presentationHEq cache fuel a' b' links
      let aa := a.getAppArgs
      let bb := b.getAppArgs
      let af := a.getAppFn.consumeMData
      let bf := b.getAppFn.consumeMData
      let sameHead ← if af == bf then pure true
        else if af.isConst && bf.isConst &&
            (af.constName?.getD `_) == (bf.constName?.getD `_) then isDefEq af bf
        else pure false
      if sameHead && aa == bb then return ← mkHEqRefl a
      if sameHead && af.isConst && (af.constName?.getD `_) == ``NatTrans && aa.size == 6 then
        let hF ← presentationHEq cache fuel aa[4]! bb[4]! links
        let hG ← presentationHEq cache fuel aa[5]! bb[5]! links
        let h ← mkAppM ``presentationNatTransCongr
          #[aa[4]!, aa[5]!, bb[4]!, bb[5]!, ← mkEqOfHEq hF, ← mkEqOfHEq hG]
        return ← mkHEqOfEq h
      if sameHead && aa.size == bb.size && !aa.isEmpty then
        let first := 0
        let c ← if let .const name levels := af then do
          match ← mkHCongrWithArityForConst? name levels aa.size with
          | some c => pure c
          | none => mkHCongrWithArity af aa.size
        else mkHCongrWithArity af aa.size
        let mut args := #[]
        for i in [first:aa.size] do
          let h ← presentationHEq cache fuel aa[i]! bb[i]! links
          let h ← if c.argKinds[i-first]! == .eq then mkEqOfHEq h else pure h
          args := args ++ #[aa[i]!,bb[i]!,h]
        let h := mkAppN c.proof args
        if (← inferType h).isHEq then return h else return ← mkHEqOfEq h
      let a' ← withTransparency .default (whnf a)
      let b' ← withTransparency .default (whnf b)
      if a' != a || b' != b then
        return ← presentationHEq cache fuel a' b' links
      let a' ← unfoldHead a
      let b' ← unfoldHead b
      if a'.isSome || b'.isSome then
        return ← presentationHEq cache fuel (a'.getD a) (b'.getD b) links
      throwError "presentation mismatch: {a.getAppFn} / {b.getAppFn}"
    cache.modify (·.insert key h)
    return h

private def leftPullCoordinates (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    sfIntrinsicDerivedPullback A p ⋙ (sfIntrinsicDerivedEquivalence X A).inverse ≅
      (sfIntrinsicDerivedEquivalence Y A).inverse ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).leftDerivedFunctor :=
  exactPullCoordinates A p ≪≫ Functor.isoWhiskerLeft _
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) p).symm

private theorem leftPullCoordinates_comp (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : proEtaleDerivedCategory Z A) :
    (sfIntrinsicDerivedEquivalence X A).inverse.map
        ((sfIntrinsicDerivedPullbackComp A f g).hom.app M) ≫
      (leftPullCoordinates A f).hom.app ((sfIntrinsicDerivedPullback A g).obj M) ≫
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor.map
        ((leftPullCoordinates A g).hom.app M) =
    (leftPullCoordinates A (f ≫ g)).hom.app M ≫
      (leftDerivedUpperStarComp
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).hom.app
          ((sfIntrinsicDerivedEquivalence Z A).inverse.obj M) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory B f).inv.naturality
    ((exactPullCoordinates A g).hom.app M)
  rw [leftDerivedUpperStarComp_hom_app]
  simp -implicitDefEqProofs only [leftPullCoordinates, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  have hn₂ := (leftDerivedUpperStarIsoMapDerivedCategory B f).inv.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory B g).inv.app
      ((sfIntrinsicDerivedEquivalence Z A).inverse.obj M))
  rw [← hn₂]
  simp -implicitDefEqProofs only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (exactPullCoordinates_comp A f g M)]
  simp -implicitDefEqProofs only [B, Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    NatTrans.comp_app,
    Category.assoc]

private theorem inverse_compositor_cancel
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {x y : A} {v w z : B} (e : x ≅ y) (q : z ≅ w)
    (a : F.obj y ⟶ v) (b : v ⟶ w) (c : F.obj x ⟶ z)
    (h : F.map e.hom ≫ a ≫ b = c ≫ q.hom) :
    a ≫ b ≫ q.inv = F.map e.inv ≫ c := by
  have he := congrArg (fun t ↦ F.map e.inv ≫ t ≫ q.inv) h
  simp -implicitDefEqProofs only [Category.assoc, ← F.map_comp_assoc, e.inv_hom_id,
    F.map_id, Category.id_comp, q.hom_inv_id, Category.comp_id] at he
  exact he

private theorem leftPullCoordinates_comp_inv (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {p : X ⟶ Z}
    (h : f ≫ g = p) (M : proEtaleDerivedCategory Z A) :
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    (leftPullCoordinates A f).hom.app ((sfIntrinsicDerivedPullback A g).obj M) ≫
        (upperStar B f).leftDerivedFunctor.map ((leftPullCoordinates A g).hom.app M) ≫
        ((leftDerivedUpperStarComp B f g).symm ≪≫
          eqToIso (congrArg (fun t ↦ (upperStar B t).leftDerivedFunctor) h)).hom.app
            ((sfIntrinsicDerivedEquivalence Z A).inverse.obj M) =
      (sfIntrinsicDerivedEquivalence X A).inverse.map
          (((sfIntrinsicDerivedPullbackComp A f g).symm ≪≫
            eqToIso (congrArg (sfIntrinsicDerivedPullback A) h)).hom.app M) ≫
        (leftPullCoordinates A p).hom.app M := by
  subst p
  dsimp only
  simp -implicitDefEqProofs only [eqToIso_refl, Iso.trans_refl, Iso.symm_hom]
  exact inverse_compositor_cancel
    (sfIntrinsicDerivedEquivalence X A).inverse
    ((sfIntrinsicDerivedPullbackComp A f g).app M)
    ((leftDerivedUpperStarComp
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).app
        ((sfIntrinsicDerivedEquivalence Z A).inverse.obj M))
    ((leftPullCoordinates A f).hom.app ((sfIntrinsicDerivedPullback A g).obj M))
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).leftDerivedFunctor.map
      ((leftPullCoordinates A g).hom.app M))
    ((leftPullCoordinates A (f ≫ g)).hom.app M)
    (leftPullCoordinates_comp A f g M)

private theorem map_iso_cancel
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {x y z w : A} {q : B} (a : x ⟶ y) (b : y ⟶ z) (e : w ≅ z)
    (p : F.obj z ⟶ q) :
    F.map (a ≫ b ≫ e.inv) ≫ F.map e.hom ≫ p = F.map (a ≫ b) ≫ p := by
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  exact congrArg (fun j ↦ F.map a ≫ F.map b ≫ j) ((F.mapIso e).inv_hom_id_assoc p)

section CoordinateNormalization

set_option maxHeartbeats 100000 in
-- The specified coefficient presentations require extra elaboration.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem pullCoordinate_eq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    {X Y : Scheme.{u}} (p : X ⟶ Y) (V : normalizedDVRDerived C.l E Y m) :
    pullCoordinate (C := C) (E := E) m p V =
      (leftPullCoordinates (Padic.coefficientExtensionRing C.l E (m + 1)) p).app V := by
  apply Iso.ext
  let := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let RX := sfIntrinsicDerivedEquivalence X A
  let RY := sfIntrinsicDerivedEquivalence Y A
  let P := finiteDerivedPullback C.l E m p
  let ep : P ≅ RY.inverse ⋙ sfFixedDerivedPullback A p ⋙ RX.functor := by
    change (sfIntrinsicPullback A p).mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence Y A).inverse.mapDerivedCategory ⋙
        sfFixedDerivedPullback A p ⋙
          (sfIntrinsicModuleEquivalence X A).functor.mapDerivedCategory
    exact Functor.mapDerivedCategoryCompIso (sfIntrinsicModuleEquivalence Y A).inverse
      (upperStar B p ⋙ (sfIntrinsicModuleEquivalence X A).functor) ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
  let q := (leftDerivedUpperStarIsoMapDerivedCategory B p).inv.app (RY.inverse.obj V)
  let w := (sfFixedDerivedPullback A p).obj (RY.inverse.obj V)
  let w' := (upperStar B p).leftDerivedFunctor.obj (RY.inverse.obj V)
  let q' := RX.functor.map q
  have hq := RX.unitIso.inv.naturality q
  change RX.inverse.map (ep.hom.app V ≫ q') ≫ RX.unitIso.inv.app w' =
    (RX.inverse.map (ep.hom.app V) ≫ RX.unitIso.inv.app w) ≫ q
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  exact congrArg (fun t ↦ RX.inverse.map (ep.hom.app V) ≫ t) hq

set_option maxHeartbeats 100000 in
-- The specified coefficient presentations require extra elaboration.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem fixedPullRealization_eq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (M : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) Y) :
    (fixedPullRealization S f M).hom =
      (realization (C := C) (E := E) (n := m + 1)
        (hn := Nat.le_add_left 1 m) X).inverse.map ((S.finitePullback f).hom.app M) ≫
      (pullCoordinate (C := C) (E := E) m f.hom.left M.obj).hom := by
  let := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let RX := sfIntrinsicDerivedEquivalence X.obj.left A
  let RY := sfIntrinsicDerivedEquivalence Y.obj.left A
  rw [finiteExactCoordinates_total, pullCoordinate_eq]
  change (RX.inverse.map ((S.finitePullback f).hom.app M) ≫
      (exactPullCoordinates A f.hom.left).hom.app M.obj) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory B f.hom.left).inv.app
          (RY.inverse.obj M.obj) =
    RX.inverse.map ((S.finitePullback f).hom.app M) ≫
      ((exactPullCoordinates A f.hom.left).hom.app M.obj ≫
        (leftDerivedUpperStarIsoMapDerivedCategory B f.hom.left).inv.app
          (RY.inverse.obj M.obj))
  exact Category.assoc _ _ _

end CoordinateNormalization

attribute [local irreducible] leftPullCoordinates
  sfIntrinsicDerivedEquivalence sfIntrinsicDerivedPullbackComp

set_option maxHeartbeats 200000 in
-- Eliminate transport before applying naturality in the derived categories.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem leftPullCoordinates_comp_naturality
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {p : X ⟶ Z}
    (h : f ≫ g = p) {V M : proEtaleDerivedCategory Z A} (l : V ⟶ M) :
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let RX := sfIntrinsicDerivedEquivalence X A
    let RY := sfIntrinsicDerivedEquivalence Y A
    let RZ := sfIntrinsicDerivedEquivalence Z A
    let Pg := sfIntrinsicDerivedPullback A g
    let Pf := sfIntrinsicDerivedPullback A p
    let Li := (upperStar B f).leftDerivedFunctor
    let q := (leftDerivedUpperStarComp B f g).symm ≪≫
      eqToIso (congrArg (fun t ↦ (upperStar B t).leftDerivedFunctor) h)
    let t := (sfIntrinsicDerivedPullbackComp A f g).symm ≪≫
      eqToIso (congrArg (sfIntrinsicDerivedPullback A) h)
    (leftPullCoordinates A f).hom.app (Pg.obj V) ≫
        Li.map (RY.inverse.map (Pg.map l) ≫ (leftPullCoordinates A g).hom.app M) ≫
        q.hom.app (RZ.inverse.obj M) =
      RX.inverse.map (t.hom.app V ≫ Pf.map l) ≫
        (leftPullCoordinates A p).hom.app M := by
  subst p
  dsimp only
  simp -implicitDefEqProofs only [eqToIso_refl, Iso.trans_refl, Iso.symm_hom]
  have hn := (leftPullCoordinates A f).hom.naturality
    ((sfIntrinsicDerivedPullback A g).map l)
  have ht := (sfIntrinsicDerivedPullbackComp A f g).inv.naturality l
  dsimp only [Functor.comp_map] at hn ht
  have hc := leftPullCoordinates_comp_inv A f g rfl M
  dsimp only at hc
  simp -implicitDefEqProofs only [eqToIso_refl, Iso.trans_refl, Iso.symm_hom] at hc
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn, hc, ← Functor.map_comp_assoc, ht]
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc]

-- Congruence separates coefficient instances without unfolding the derived functors.
set_option maxHeartbeats 1200000 in
-- The ambient and normalized categories have several coefficient presentation wrappers.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
private theorem pullCoordinate_compositor
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (M : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) Y)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (l : V ≅ M.obj) :
    let A := Padic.coefficientExtensionRing C.l E (m + 1)
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let RX := sfIntrinsicDerivedEquivalence X.obj.left A
    let RY := sfIntrinsicDerivedEquivalence Y.obj.left A
    let RZ := sfIntrinsicDerivedEquivalence c.Z A
    let Pg := finiteDerivedPullback C.l E m c.g
    ((pullCoordinate (C := C) (E := E) m c.i (Pg.obj V)).hom ≫
        (upperStar B c.i).leftDerivedFunctor.map
          (RZ.inverse.map (Pg.map l.hom) ≫
            (pullCoordinate (C := C) (E := E) m c.g M.obj).hom)) ≫
        (leftDerivedUpperStarCompactificationIso B c).hom.app (RY.inverse.obj M.obj) =
      RX.inverse.map
        ((((SystemProjectionFormula.finitePullComp C.l E c.i c.g m).symm ≪≫
          eqToIso (congrArg (finiteDerivedPullback C.l E m) c.comm.symm)).hom.app V) ≫
          (finiteDerivedPullback C.l E m f.hom.left).map l.hom ≫
          (S.finitePullback f).inv.app M) ≫ (fixedPullRealization S f M).hom := by
  let := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let RX := sfIntrinsicDerivedEquivalence X.obj.left A
  let Pf := sfIntrinsicDerivedPullback A f.hom.left
  let t := ((sfIntrinsicDerivedPullbackComp A c.i c.g).symm ≪≫
    eqToIso (congrArg (sfIntrinsicDerivedPullback A) c.comm.symm)).hom.app V
  have hc := leftPullCoordinates_comp_naturality A c.i c.g c.comm.symm
    (V := V) (M := M.obj) l.hom
  have he := (map_iso_cancel RX.inverse t (Pf.map l.hom) ((S.finitePullback f).app M)
    ((leftPullCoordinates A f.hom.left).hom.app M.obj)).symm
  -- Expose the outer equality without unfolding the comparison functors.
  change _ = _
  conv_rhs => rw [fixedPullRealization_eq]
  simp -implicitDefEqProofs only [pullCoordinate_eq]
  simp -implicitDefEqProofs only [Category.assoc]
  have hr := hc.trans he
  run_tac Lean.Elab.Tactic.withMainContext do
    let some r := (← Lean.getLCtx).findFromUserName? `hr |
      throwError "missing compositor normalization"
    let g ← Lean.Elab.Tactic.getMainGoal
    let src ← Lean.Meta.inferType r.toExpr
    let tgt ← g.getType
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let h ← presentationHEq cache 160 src tgt #[]
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[← Lean.Meta.mkEqOfHEq h, r.toExpr])
    Lean.Elab.Tactic.replaceMainGoal []

private theorem support_target_normalization
    {A B D : Type*} [Category A] [Category B] [Category D]
    (R : A ≌ B) (F : B ⥤ D) (G : A ⥤ D) (s : R.functor ⋙ F ≅ G)
    {P Q : A} {Z : D} (e : P ≅ Q) (σ : Z ≅ F.obj (R.functor.obj P)) :
    σ ≪≫ F.mapIso (R.counitIso.app (R.functor.obj P)).symm ≪≫
        s.app (R.inverse.obj (R.functor.obj P)) ≪≫
        G.mapIso ((R.unitIso.app P).symm ≪≫ e) =
      σ ≪≫ s.app P ≪≫ G.mapIso e := by
  apply Iso.ext
  simp -implicitDefEqProofs only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp]
  change σ.hom ≫ F.map (R.counitIso.inv.app (R.functor.obj P)) ≫
      s.hom.app (R.inverse.obj (R.functor.obj P)) ≫ G.map (R.unitIso.inv.app P) ≫
        G.map e.hom = σ.hom ≫ s.hom.app P ≫ G.map e.hom
  have hn := s.hom.naturality (R.unitIso.inv.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  calc
    _ = σ.hom ≫ F.map (R.counitIso.inv.app (R.functor.obj P)) ≫
        (F.map (R.functor.map (R.unitIso.inv.app P)) ≫ s.hom.app P) ≫
          G.map e.hom := by
      simpa -implicitDefEqProofs only [Category.assoc] using congrArg
        (fun t ↦ σ.hom ≫ F.map (R.counitIso.inv.app (R.functor.obj P)) ≫ t ≫
          G.map e.hom) hn.symm
    _ = _ := by
      rw [Category.assoc, ← F.map_comp_assoc, ← R.counit_app_functor]
      simp

private def tensorPresentation
    {A B K L M N : Type*} [Category* A] [Category* B] [Category* K]
    [Category* L] [Category* M] [Category* N]
    (J : A ⥤ K) (H : B ⥤ L) (T : K ⥤ L ⥤ M) (V : M ⥤ N) :
    Functor.uncurry.obj ((Functor.postcompose₂.obj V).obj
      ((((Functor.whiskeringLeft₂ _).obj J).obj H).obj T)) ≅
        J.prod H ⋙ Functor.uncurry.obj T ⋙ V :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp [Functor.uncurry, Functor.map_comp])

private theorem tensorPresentation_map
    {A B K L M N : Type*} [Category* A] [Category* B] [Category* K]
    [Category* L] [Category* M] [Category* N]
    (J : A ⥤ K) (H : B ⥤ L) (T : K ⥤ L ⥤ M) (V : M ⥤ N)
    {X Y : A × B} (a : X ⟶ Y) :
    (J.prod H ⋙ Functor.uncurry.obj T ⋙ V).map a =
      (Functor.uncurry.obj ((Functor.postcompose₂.obj V).obj
        ((((Functor.whiskeringLeft₂ _).obj J).obj H).obj T))).map a := by
  have hn := (tensorPresentation J H T V).hom.naturality a
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _ at hn
  simpa -implicitDefEqProofs only [Category.comp_id, Category.id_comp] using hn.symm

private theorem uncurry_map_snd
    {A : Type*} [Category A] (T : A ⥤ A ⥤ A) {K L L' : A} (a : L ⟶ L') :
    (Functor.uncurry.obj T).map (Prod.mkHom (𝟙 K) a) = (T.obj K).map a := by
  simp -implicitDefEqProofs only [Functor.uncurry_obj_map, T.map_id, NatTrans.id_app,
    Category.id_comp]

private theorem tensor_compositor_paste
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R : A ≌ B) (G : B ⥤ C) (H : A ⥤ C) (T : A × A ⥤ A)
    (I : B × B ⥤ B)
    (e : I ≅ R.inverse.prod R.inverse ⋙ T ⋙ R.functor)
    (α : R.functor ⋙ G ≅ H)
    {u v w k z : B} {q r : A} (a : u ⟶ k) (t : v ⟶ w) (b : w ⟶ z)
    (d : R.inverse.obj v ⟶ q) (c : q ⟶ r) (p : R.inverse.obj z ⟶ r)
    (hd : d ≫ c = R.inverse.map (t ≫ b) ≫ p) :
    G.map (e.hom.app (u,v)) ≫ α.hom.app (T.obj (R.inverse.obj u,R.inverse.obj v)) ≫
      H.map (T.map (Prod.mkHom (R.inverse.map a) d)) ≫
      H.map (T.map (Prod.mkHom (𝟙 (R.inverse.obj k)) c)) =
    G.map (I.map (Prod.mkHom (𝟙 u) t)) ≫ G.map (e.hom.app (u,w)) ≫
      G.map ((R.inverse.prod R.inverse ⋙ T ⋙ R.functor).map (Prod.mkHom a b)) ≫
      α.hom.app (T.obj (R.inverse.obj k,R.inverse.obj z)) ≫
      H.map (T.map (Prod.mkHom (𝟙 (R.inverse.obj k)) p)) := by
  rw [← G.map_comp_assoc, e.hom.naturality (Prod.mkHom (𝟙 u) t)]
  simp -implicitDefEqProofs only [Functor.comp_map, Functor.prod_map]
  rw [G.map_comp]
  simp -implicitDefEqProofs only [Category.assoc]
  apply congrArg (fun s ↦ G.map (e.hom.app (u,v)) ≫ s)
  have hn₁ := α.hom.naturality
    (T.map (Prod.mkHom (R.inverse.map a) (R.inverse.map b)))
  have hn₂ := α.hom.naturality
    (T.map (Prod.mkHom (R.inverse.map (𝟙 u)) (R.inverse.map t)))
  dsimp only [Functor.comp_map] at hn₁ hn₂
  rw [reassoc_of% hn₁, reassoc_of% hn₂]
  apply congrArg (fun s ↦ α.hom.app (T.obj (R.inverse.obj u,R.inverse.obj v)) ≫ s)
  rw [← H.map_comp, ← H.map_comp, ← H.map_comp]
  congr 1
  rw [← T.map_comp, ← T.map_comp, ← T.map_comp]
  congr 1
  ext
  · simp
  · change d ≫ c = R.inverse.map t ≫ R.inverse.map b ≫ p
    simpa -implicitDefEqProofs only [Functor.map_comp, Category.assoc] using hd

private theorem curried_tensor_compositor_paste
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R : A ≌ B) (F : B ⥤ C) (G : A ⥤ C) (TX : A ⥤ A ⥤ A)
    (I : B × B ⥤ B)
    (e : I ≅ Functor.uncurry.obj ((Functor.postcompose₂.obj R.functor).obj
      ((((Functor.whiskeringLeft₂ _).obj R.inverse).obj R.inverse).obj TX)))
    (α : R.functor ⋙ F ≅ G)
    {u v w k z : B} {q r : A} (a : u ⟶ k) (t : v ⟶ w) (b : w ⟶ z)
    (d : R.inverse.obj v ⟶ q) (c : q ⟶ r) (p : R.inverse.obj z ⟶ r)
    (hd : d ≫ c = R.inverse.map (t ≫ b) ≫ p) :
    F.map (e.hom.app (u,v)) ≫
      α.hom.app ((TX.obj (R.inverse.obj u)).obj (R.inverse.obj v)) ≫
      G.map ((Functor.uncurry.obj TX).map (Prod.mkHom (R.inverse.map a) d)) ≫
      G.map ((TX.obj (R.inverse.obj k)).map c) =
    F.map (I.map (Prod.mkHom (𝟙 u) t)) ≫ F.map (e.hom.app (u,w)) ≫
      F.map ((Functor.uncurry.obj ((Functor.postcompose₂.obj R.functor).obj
        ((((Functor.whiskeringLeft₂ _).obj R.inverse).obj R.inverse).obj TX))).map
          (Prod.mkHom a b)) ≫
      α.hom.app ((TX.obj (R.inverse.obj k)).obj (R.inverse.obj z)) ≫
      G.map ((TX.obj (R.inverse.obj k)).map p) := by
  let τ := e ≪≫ tensorPresentation R.inverse R.inverse TX R.functor
  have hp := tensor_compositor_paste R F G (Functor.uncurry.obj TX) I τ α a t b d c p hd
  have hτ (Z : B × B) : τ.hom.app Z = e.hom.app Z := by
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hJ := tensorPresentation_map R.inverse R.inverse TX R.functor (Prod.mkHom a b)
  simp only [hτ, hJ, uncurry_map_snd, Functor.comp_obj, Functor.uncurry_obj_obj] at hp
  exact hp

private theorem curried_tensor_finish
    {A B C : Type*} [Category A] [Category B] [Category C]
    (R : A ≌ B) (F : B ⥤ C) (G : A ⥤ C) (TX : A ⥤ A ⥤ A)
    (I : B × B ⥤ B)
    (e : I ≅ Functor.uncurry.obj ((Functor.postcompose₂.obj R.functor).obj
      ((((Functor.whiskeringLeft₂ _).obj R.inverse).obj R.inverse).obj TX)))
    (α : R.functor ⋙ F ≅ G)
    {u v w k z : B} {q r : A} {Z : C}
    (a : u ⟶ k) (t : v ⟶ w) (b : w ⟶ z)
    (d : R.inverse.obj v ⟶ q) (c : q ⟶ r) (p : R.inverse.obj z ≅ r)
    (hd : d ≫ c = R.inverse.map (t ≫ b) ≫ p.hom)
    (σ : Z ≅ F.obj (R.functor.obj ((TX.obj (R.inverse.obj k)).obj (R.inverse.obj z))))
    (ψ : Z ≅ G.obj ((TX.obj (R.inverse.obj k)).obj r))
    (hψ : ψ = σ ≪≫ α.app ((TX.obj (R.inverse.obj k)).obj (R.inverse.obj z)) ≪≫
      G.mapIso ((TX.obj (R.inverse.obj k)).mapIso p)) :
    (F.map (e.hom.app (u,v)) ≫
      α.hom.app ((TX.obj (R.inverse.obj u)).obj (R.inverse.obj v)) ≫
      G.map ((Functor.uncurry.obj TX).map (Prod.mkHom (R.inverse.map a) d))) ≫
      G.map ((TX.obj (R.inverse.obj k)).map c) ≫ ψ.inv =
    F.map (I.map (Prod.mkHom (𝟙 u) t)) ≫
      F.map (e.hom.app (u,w) ≫
        (Functor.uncurry.obj ((Functor.postcompose₂.obj R.functor).obj
          ((((Functor.whiskeringLeft₂ _).obj R.inverse).obj R.inverse).obj TX))).map
            (Prod.mkHom a b)) ≫ σ.inv := by
  simp only [Category.assoc]
  have hp := curried_tensor_compositor_paste R F G TX I e α a t b d c p.hom hd
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Iso.comp_inv_eq, hψ]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, σ.inv_hom_id_assoc]
  exact hp

set_option maxHeartbeats 400000 in
-- The final tensor paste uses the specified coefficient presentations.
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- The compositor coordinate square after open tensor. Only inverse-image
composition, tensor naturality and the constructible target comparison occur.

Source: Stacks 03D2, 0D6D; fix-prop-projection-formula.proof.md, same-map sentence.
(blueprint: lem-sf-finite-intrinsic-projection-compositor-square).

Proof: expand the two unary pullCoordinate comparisons in beforeCompositor. The
ordinary intrinsic inverse-image compositor is the fixed-scalar compositor with
one coefficient unit inserted at the middle scheme. Exact localization preserves
this composition: use naturality and associativity of mapDerivedCategoryCompIso
and compatibility with mapDerivedCategoryNatIso. The inserted unit cancels with
the inverse unit in pullCoordinate. The exact-to-left-derived comparison identifies
the result with leftDerivedUpperStarComp, and transport along c.comm gives the
compactification compositor. Tensor naturality moves this equality past k and l.
Apply compact support and its realization comparison. Expand targetComparison,
supportRealization, projectionTensorTargetRealization and fixedPullRealization.
Naturality moves the coefficient units to adjacent inverse units, and the triangle
identities cancel them. The finitePullback and finiteSupport isomorphisms cancel
with their inverses, leaving the displayed constructible-coordinate target map.
No open tensor map and no proper projection mate occur. Identity compositors,
zero inputs, empty schemes and m=0 use the same naturality and triangle identities. -/
theorem finiteIntrinsicProjectionCompositorSquare
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
    (L : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) Y.obj.left)
    (U : normalizedDVRDerived C.l E X.obj.left m)
    (V : normalizedDVRDerived C.l E Y.obj.left m) (k : U ≅ K.obj) (l : V ≅ L.obj) :
    beforeCompositor m f c K L U V k l ≫ fixedCompositorPart m f c K L ≫
        (targetComparison S f c K L).inv =
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing C.l E (m + 1)) c).map
          ((finiteIntrinsicDerivedTensor C.l E X.obj.left m).map
            (Prod.mkHom (𝟙 U)
              (((SystemProjectionFormula.finitePullComp C.l E c.i c.g m).symm ≪≫
                eqToIso (congrArg (finiteDerivedPullback C.l E m) c.comm.symm)).hom.app V))) ≫
      ((sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).map
        ((canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X).hom.app
          (U, (finiteDerivedPullback C.l E m f.hom.left).obj V) ≫
          (evaluatedTensor (C := C) (E := E) m X).map
            (Prod.mkHom k.hom ((finiteDerivedPullback C.l E m f.hom.left).map l.hom ≫
              (S.finitePullback f).inv.app ⟨L.obj, L.property.1⟩))) ≫
        (S.finiteSupport f c).inv.app
          (((partialTensor S X).obj K).obj ((torPull S f).obj L))) := by
  let := Padic.finite_coefficientExtensionRing C.l E (m + 1) (Nat.le_add_left 1 m)
  let A := Padic.coefficientExtensionRing C.l E (m + 1)
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let RX := sfIntrinsicDerivedEquivalence X.obj.left A
  let RY := sfIntrinsicDerivedEquivalence Y.obj.left A
  let RZ := sfIntrinsicDerivedEquivalence c.Z A
  let F := sfAmbientCompactSupportCandidate A c
  let H := sfFixedCompactSupport A c
  let G := H ⋙ RY.functor
  let TX := fixedTensor (C := C) (E := E) (n := m + 1) X
  let T := Functor.uncurry.obj TX
  let I := finiteIntrinsicDerivedTensor C.l E X.obj.left m
  let s : RX.functor ⋙ F ≅ G := sfIntrinsicCompactSupportComparison A c
  let Pg := finiteDerivedPullback C.l E m c.g
  let Pf := finiteDerivedPullback C.l E m f.hom.left
  let M : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) Y :=
    ⟨L.obj, L.property.1⟩
  let N := ((S.finite.pull f).obj M).obj
  let W := ((partialTensor S X).obj K).obj ((torPull S f).obj L)
  let Q := T.obj (RX.inverse.obj K.obj, RX.inverse.obj N)
  let e := (TX.obj (RX.inverse.obj K.obj)).mapIso (fixedPullRealization S f M)
  let σ := (S.finiteSupport f c).app W
  have ht : targetComparison S f c K L = σ ≪≫ s.app Q ≪≫ G.mapIso e := by
    unfold targetComparison supportRealization projectionTensorTargetRealization
    change (σ ≪≫ F.mapIso (RX.counitIso.app (RX.functor.obj Q)).symm ≪≫
      s.app (RX.inverse.obj (RX.functor.obj Q))) ≪≫
      RY.functor.mapIso (H.mapIso ((RX.unitIso.app Q).symm ≪≫ e)) = _
    apply Iso.ext
    have hnorm := congrArg (fun j ↦ j.hom) (support_target_normalization RX F G s e σ)
    simpa -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom,
      Functor.comp_map, Functor.comp_obj, G, Category.assoc, Q, T, N, M, RX, RY,
      A, realization, sixFunctorFiniteRealization, Functor.uncurry_obj_obj] using hnorm
  -- Paste the normalized support comparison with the unary compositor equality.
  let t := ((SystemProjectionFormula.finitePullComp C.l E c.i c.g m).symm ≪≫
    eqToIso (congrArg (finiteDerivedPullback C.l E m) c.comm.symm)).hom.app V
  let b := Pf.map l.hom ≫ (S.finitePullback f).inv.app M
  let d := (pullCoordinate (C := C) (E := E) m c.i (Pg.obj V)).hom ≫
    (upperStar B c.i).leftDerivedFunctor.map
      (RZ.inverse.map (Pg.map l.hom) ≫
        (pullCoordinate (C := C) (E := E) m c.g L.obj).hom)
  let q := (leftDerivedUpperStarCompactificationIso B c).hom.app (RY.inverse.obj L.obj)
  have hd := pullCoordinate_compositor m S f c M V l
  have hs := curried_tensor_finish RX F G TX I
    (canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X) s
    k.hom t b d q (fixedPullRealization S f M) (by
      have hcoord := hd
      run_tac Lean.Elab.Tactic.withMainContext do
        let some r := (← Lean.getLCtx).findFromUserName? `hcoord |
          throwError "missing coordinate proof"
        let g ← Lean.Elab.Tactic.getMainGoal
        let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
        let h ← presentationHEq cache 160 (← Lean.Meta.inferType r.toExpr)
          (← g.getType) #[]
        g.assign (← Lean.Meta.mkAppM ``Eq.mp #[← Lean.Meta.mkEqOfHEq h, r.toExpr])
        Lean.Elab.Tactic.replaceMainGoal []) σ (targetComparison S f c K L) ht
  run_tac Lean.Elab.Tactic.withMainContext do
    let some r := (← Lean.getLCtx).findFromUserName? `hs |
      throwError "missing tensor calculation"
    let g ← Lean.Elab.Tactic.getMainGoal
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let h ← presentationHEq cache 160 (← Lean.Meta.inferType r.toExpr)
      (← g.getType) #[]
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[← Lean.Meta.mkEqOfHEq h, r.toExpr])
    Lean.Elab.Tactic.replaceMainGoal []

end WeilConjectures.IntegralProjectionReduction
