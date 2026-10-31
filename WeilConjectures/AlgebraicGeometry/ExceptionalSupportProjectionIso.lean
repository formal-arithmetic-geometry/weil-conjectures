/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantSupportProjection
public import WeilConjectures.AlgebraicGeometry.AmbientExceptionalRightAdjoint

import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport

/-!
# Scalar restricted constant support projection

Source: Stacks Tag 0GL6 and the coefficientwise support comparison.
(blueprint: lem-exc-support-constant-projection-after-restriction)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

attribute [local instance 2000] CommRing.toRing in
@[irreducible] private noncomputable def supportRealizationIso
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfAmbientCompactSupportCandidate A c ≅
      ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EZ := sfIntrinsicModuleEquivalence c.Z A
  let J := ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i
  let o : EX.functor ⋙ sfIntrinsicExtensionByZero c.i A ≅ J ⋙ EZ.functor :=
    EX.funInvIdAssoc (J ⋙ EZ.functor)
  let od := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso o ≪≫ Functor.mapDerivedCategoryCompIso _ _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight od _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

attribute [local instance 2000] CommRing.toRing in
private theorem support_isLeftAdjoint
    {A : Type u} [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    {G : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A}
    (_a : sfAmbientCompactSupportCandidate A c ⊣ G) :
    (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).IsLeftAdjoint := by
  let EX := sfIntrinsicDerivedEquivalence X A
  let EY := sfIntrinsicDerivedEquivalence Y A
  let F := ProEtale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c
  have : (sfAmbientCompactSupportCandidate A c).IsLeftAdjoint := _a.isLeftAdjoint
  let e : (EX.functor ⋙ sfAmbientCompactSupportCandidate A c) ⋙ EY.inverse ≅ F :=
    Functor.isoWhiskerRight (supportRealizationIso A c) EY.inverse ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F EY.unitIso.symm ≪≫
      Functor.rightUnitor _
  exact Functor.isLeftAdjoint_of_iso e

attribute [local instance 2000] CommRing.toRing in
attribute [local instance 2000] isNoetherian_of_finite in
attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
private theorem projection_of_leftAdjoint
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).IsLeftAdjoint]
    (K : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (M : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).app
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj K)).app
      ((constantSheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).mapDerivedCategory.obj M)) := by
  have hp := ProEtale.isIso_constantSupportProjection (ULift.{u + 1, u} A) c K M
  -- The generic theorem uses Mathlib's module-category Grothendieck instance.
  -- Abstract the shortcut instance before transporting along proof irrelevance;
  -- direct conversion unfolds the derived projection and times out in the kernel.
  revert hp
  generalize ModuleCat.isGrothendieckAbelian_of_commRing (ULift.{u + 1, u} A) = i
  intro hp
  exact (Subsingleton.elim _ i) ▸ hp

section InstanceTransport
open Lean Meta Elab Tactic

private theorem instanceProofsHEq {P Q : Prop} (p : P) (q : Q) : HEq p q := by
  have h : P = Q := propext ⟨fun _ ↦ q, fun _ ↦ p⟩
  cases h
  rfl

private meta def instanceCongr
    (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) : Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "instance congruence depth exhausted"
  | fuel + 1, a, b => do
    let a := (← instantiateMVars a).headBeta.consumeMData
    let b := (← instantiateMVars b).headBeta.consumeMData
    if let some h := (← cache.get)[(a, b)]? then return h
    let h ← do
      if a == b then return ← mkHEqRefl a
      if ← isProp (← inferType a) then
        return ← mkAppM ``instanceProofsHEq #[a, b]
      if let .letE _ _ val body _ := a then
        return ← instanceCongr cache fuel (body.instantiate1 val) b
      if let .letE _ _ val body _ := b then
        return ← instanceCongr cache fuel a (body.instantiate1 val)
      if a.isFVar then
        if let some val := ((← getLCtx).get! a.fvarId!).value? then
          return ← instanceCongr cache fuel val b
      if b.isFVar then
        if let some val := ((← getLCtx).get! b.fvarId!).value? then
          return ← instanceCongr cache fuel a val
      let af := a.getAppFn
      let bf := b.getAppFn
      if af.isMData then
        return ← instanceCongr cache fuel (mkAppN af.consumeMData a.getAppArgs) b
      if bf.isMData then
        return ← instanceCongr cache fuel a (mkAppN bf.consumeMData b.getAppArgs)
      let sharedType := af.isConstOf ``DerivedCategory ||
        af.isConstOf ``instCategoryDerivedCategory || af.isConstOf ``Sheaf ||
        af.isConstOf ``CategoryTheory.ObjectProperty.FullSubcategory.category ||
        af.isConstOf ``Functor.category || af.isConstOf ``CategoryTheory.Functor ||
        af.isConstOf ``HasDerivedCategory.ofIsGrothendieckAbelian
      if sharedType then
        if ← withReducible (isDefEq a b) then return ← mkHEqRefl a
      if af == bf && a.getAppArgs.size == b.getAppArgs.size then
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let ct ← mkHCongrWithArity af aa.size
        let mut ps := #[]
        for i in [:aa.size] do
          let mut h ← instanceCongr cache fuel aa[i]! bb[i]!
          if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
          ps := ps ++ #[aa[i]!, bb[i]!, h]
        let pf := mkAppN ct.proof ps
        if (← inferType pf).isHEq then return pf
        return ← mkAppM ``heq_of_eq #[pf]
      if af.isConstOf ``CommRing.toRing || bf.isConstOf ``CommRing.toRing then
        unless ← isDefEq a b do throwError "coefficient rings differ"
        return ← mkHEqRefl a
      throwError "unmatched instance data: {a} versus {b}"
    cache.modify (·.insert (a, b) h)
    return h

private meta def transportInstances (userName : Name) : TacticM Unit :=
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let ds := (← getLCtx).decls.toList.filterMap id
    let some d := ds.find? (fun d ↦ d.userName.eraseMacroScopes == userName)
      | throwError "no comparison named {userName}"
    let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
    let q ← instanceCongr cache 500 target (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf
end InstanceTransport

/-- The constant coefficient projection at the scalar-restricted coefficient object is an
isomorphism under the ambient support adjunction.
Source: Stacks Tag 0GL6; (blueprint: lem-exc-support-constant-projection-after-restriction).
Proof: use the ambient support adjunction to obtain the discrete-colimit preservation
hypothesis, then apply the generic constant-support projection theorem to the scalar-restricted
constant coefficient object. -/
theorem exceptionalSupport_constantProjection_isIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {G : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory X A}
    (_a : sfAmbientCompactSupportCandidate A c ⊣ G)
    (K : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    IsIso (((ProEtale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).app
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj K)).app
      ((constantSheaf (ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ModuleCat.restrictScalars.{u + 1} φ.ulift).obj
            (ModuleCat.of (ULift.{u + 1, u} B) (ULift.{u + 1, u} B)))))) := by
  have : (ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).IsLeftAdjoint :=
    support_isLeftAdjoint c _a
  have hp := projection_of_leftAdjoint A c K
      ((DerivedCategory.singleFunctor _ 0).obj
        ((ModuleCat.restrictScalars.{u + 1} φ.ulift).obj
          (ModuleCat.of (ULift.{u + 1, u} B) (ULift.{u + 1, u} B))))
  run_tac transportInstances `hp


end WeilConjectures
