/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionData
import Mathlib.CategoryTheory.Preadditive.Biproducts
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsTransitionExistence
import all WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation

/-! # The normalized inverse-image transition

The finite ordinary-unit law fixes the restriction/pullback square. Localizing and
transposing that square gives compatibility with the actual scalar-coordinate reductions.
Source: blueprint integral direct-image proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Use the coefficient-universe sheafification of the source tower models.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpShriekTransition
attribute [local implicit_reducible] SemilinearSections.hasDerived
  SemilinearSections.moduleAbelian scalarExtensionFunctor
attribute [local irreducible] quotientMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard Padic Padic.coefficientExtensionIntegers
  proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleConstantRingComparison proEtaleRingDirectImageMap
attribute [local implicit_reducible] SheafOfModules.restrictScalars
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  PresheafOfModules.presheaf ModuleCat.restrictScalars

-- Congruence aligns category instances using proof irrelevance and abelian uniqueness,
-- without expanding derived-functor bodies. This follows the private transport in
-- Sheaf.Paper.TowerCompositorFiniteEvaluation; every generated term is kernel checked.
section InstanceTransport
open Lean Meta Elab Tactic CategoryTheory

private theorem instanceProofsHEq {P Q : Prop} (p : P) (q : Q) : HEq p q := by
  have h : P = Q := propext ⟨fun _ ↦ q, fun _ ↦ p⟩
  cases h
  rfl

/-- Biproducts determine the additive structure; the remaining abelian fields are proofs. -/
private theorem abelian_eq {C : Type*} [Category C] (a b : Abelian C) : a = b := by
  let _ := a
  have hp : a.toPreadditive = b.toPreadditive := Subsingleton.elim _ _
  cases a
  cases b
  cases hp
  rfl

private meta def nameCoordinateProjection (e : Expr) : MetaM Expr := do
  let .proj n i f := e.getAppFn | return e
  let name := if n == ``CategoryTheory.Functor then
      if i == 0 then ``Functor.obj else ``Functor.map
    else if n == ``Iso then if i == 0 then ``Iso.hom else ``Iso.inv
    else if n == ``NatTrans && i == 0 then ``NatTrans.app
    else if n == ``ObjectProperty.FullSubcategory && i == 0 then
      ``ObjectProperty.FullSubcategory.obj
    else if n == ``InducedCategory.Hom && i == 0 then ``InducedCategory.Hom.hom
    else Name.anonymous
  if name.isAnonymous then return e
  let ty ← inferType f
  let ty ← if ty.getAppFn.isConstOf n then pure ty else whnf ty
  let p := mkAppN (.const name ty.getAppFn.constLevels!) (ty.getAppArgs.push f)
  return mkAppN p e.getAppArgs

private meta def reduceCoordinateObject : Nat → Expr → MetaM Expr
  | 0, e => pure e
  | fuel + 1, e => do
    let fn := e.getAppFn
    let args := e.getAppArgs
    if fn.isConstOf ``Functor.obj && args.size == 6 then
      let f := args[4]!
      let h := f.getAppFn
      if h.isConstOf ``Functor.comp || h.isConstOf ``ObjectProperty.ι ||
          h.isConstOf ``ObjectProperty.lift || h.isConstOf ``Functor.id then
        if let some f' ← withDefault <| unfoldDefinition? f then
          let e' ← whnfCore (mkApp (.proj ``CategoryTheory.Functor 0 f') args[5]!)
          return ← reduceCoordinateObject fuel (← nameCoordinateProjection e')
    if fn.isConstOf ``ObjectProperty.FullSubcategory.obj then
      let arg := args.back!
      let arg' ← reduceCoordinateObject fuel (← nameCoordinateProjection arg)
      if arg' != arg then
        let e' := mkAppN fn (args.set! (args.size - 1) arg')
        if let some e'' ← withDefault <| unfoldDefinition? e' then
          return ← reduceCoordinateObject fuel (← whnfCore e'')
      if let some e' ← Lean.Expr.reduceProjStruct? e then return e'
    return e

private meta def instanceCongr
    (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr))
    (norm : Bool) : Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "instance congruence depth exhausted"
  | fuel + 1, a, b => do
    let a := (← instantiateMVars a).headBeta.consumeMData
    let b := (← instantiateMVars b).headBeta.consumeMData
    let entries ← cache.get
    if let some h := entries[(a, b)]? then return h
    let h ← do
      if a == b then return ← mkHEqRefl a
      let ta ← inferType a
      if ← isProp ta then
        return ← mkAppM ``instanceProofsHEq #[a, b]
      if ta.getAppFn.isConstOf ``Abelian &&
          (← inferType b).getAppFn.isConstOf ``Abelian then
        return ← mkAppM ``heq_of_eq #[← mkAppM ``abelian_eq #[a, b]]
      if let .letE _ _ val body _ := a then
        return ← instanceCongr cache norm fuel (body.instantiate1 val) b
      if let .letE _ _ val body _ := b then
        return ← instanceCongr cache norm fuel a (body.instantiate1 val)
      if a.isFVar then
        if let some val := ((← getLCtx).get! a.fvarId!).value? then
          return ← instanceCongr cache norm fuel val b
      if b.isFVar then
        if let some val := ((← getLCtx).get! b.fvarId!).value? then
          return ← instanceCongr cache norm fuel a val
      let af := a.getAppFn
      let bf := b.getAppFn
      if af.isMData then
        return ← instanceCongr cache norm fuel (mkAppN af.consumeMData a.getAppArgs) b
      if bf.isMData then
        return ← instanceCongr cache norm fuel a (mkAppN bf.consumeMData b.getAppArgs)
      if norm then
        let a' ← nameCoordinateProjection a
        let b' ← nameCoordinateProjection b
        if a' != a || b' != b then return ← instanceCongr cache norm fuel a' b'
        let a' ← reduceCoordinateObject 30 a
        let b' ← reduceCoordinateObject 30 b
        if a' != a || b' != b then return ← instanceCongr cache norm fuel a' b'
      if af == bf && a.getAppArgs.size == b.getAppArgs.size then
        let aa := a.getAppArgs
        let bb := b.getAppArgs
        let ct ← mkHCongrWithArity af aa.size
        let cp ← mkAuxTheorem ct.type ct.proof (zetaDelta := true)
        let mut ps := #[]
        for i in [:aa.size] do
          let mut h ← instanceCongr cache norm fuel aa[i]! bb[i]!
          if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
          ps := ps ++ #[aa[i]!, bb[i]!, h]
        let pf := mkAppN cp ps
        if (← inferType pf).isHEq then return pf
        return ← mkAppM ``heq_of_eq #[pf]
      if af.isConstOf ``Functor.id then
        if let some a' ← withDefault <| unfoldDefinition? a then
          return ← instanceCongr cache norm fuel a' b
      if bf.isConstOf ``Functor.id then
        if let some b' ← withDefault <| unfoldDefinition? b then
          return ← instanceCongr cache norm fuel a b'
      if af != bf then
        if af.isConstOf ``WeilConjectures.SemilinearSections.moduleAbelian then
          if let some a' ← withDefault <| unfoldDefinition? a then
            return ← instanceCongr cache norm fuel a' b
        if bf.isConstOf ``WeilConjectures.SemilinearSections.moduleAbelian then
          if let some b' ← withDefault <| unfoldDefinition? b then
            return ← instanceCongr cache norm fuel a b'
        if af.isConstOf ``scalarExtensionFunctor ||
            af.isConstOf ``proEtaleConstantRingDerivedPullback ||
            af.isConstOf ``proEtaleRingDerivedPullback then
          if let some a' ← withDefault <| unfoldDefinition? a then
            return ← instanceCongr cache norm fuel a' b
        if bf.isConstOf ``scalarExtensionFunctor ||
            bf.isConstOf ``proEtaleConstantRingDerivedPullback ||
            bf.isConstOf ``proEtaleRingDerivedPullback then
          if let some b' ← withDefault <| unfoldDefinition? b then
            return ← instanceCongr cache norm fuel a b'
      if af != bf then
        if af.isConstOf ``AlgebraicGeometry.Scheme.ProjectionRestriction.derived ||
            af.isConstOf ``WeilConjectures.SemilinearSections.hasDerived ||
            af.isConstOf ``AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory ||
            af.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory then
          if let some a' ← withDefault <| unfoldDefinition? a then
            return ← instanceCongr cache norm fuel a' b
        if bf.isConstOf ``AlgebraicGeometry.Scheme.ProjectionRestriction.derived ||
            bf.isConstOf ``WeilConjectures.SemilinearSections.hasDerived ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory ||
            bf.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory then
          if let some b' ← withDefault <| unfoldDefinition? b then
            return ← instanceCongr cache norm fuel a b'
      if af.isConstOf ``CommRing.toRing || bf.isConstOf ``CommRing.toRing then
        unless ← isDefEq a b do throwError "coefficient rings differ"
        return ← mkHEqRefl a
      if ← withReducible (isDefEq a b) then return ← mkHEqRefl a
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
    let q ← instanceCongr cache true 500 target (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf
end InstanceTransport

section
attribute [local instance 100000] SemilinearSections.moduleAbelian SemilinearSections.hasDerived

private abbrev transportedTransition (T : Scheme.{u})
    (B : ℕ → Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (τ : ∀ k, B (k + 1) ⟶ B k) {m n : ℕ} (h : m ≤ n)
    (α : B n ⟶ B m)
    (e : SemilinearSections.coefficientMap.{u + 1, u, u + 1} (ProEt.topology T) B τ h = α) :=
  SemilinearSections.transition.{u + 1, u, u + 1} (ProEt.topology T) B τ h ≫
    whiskerLeft (SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology T) B τ m)
      (eqToIso (congrArg (fun a ↦ SemilinearSections.res.{u + 1, u, u + 1} a) e)).hom

private abbrev transportedDerivedTransition (T : Scheme.{u})
    (B : ℕ → Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (τ : ∀ k, B (k + 1) ⟶ B k) {m n : ℕ} (h : m ≤ n)
    (α : B n ⟶ B m)
    (e : SemilinearSections.coefficientMap.{u + 1, u, u + 1} (ProEt.topology T) B τ h = α) :=
  SemilinearSections.derivedTransition.{u + 1, u, u + 1} (ProEt.topology T) B τ h ≫
    whiskerLeft (SemilinearSections.e.{u + 1, u, u + 1} (ProEt.topology T) B τ m)
      (eqToIso (congrArg (fun a ↦ SemilinearSections.resD.{u + 1, u, u + 1} a) e)).hom

set_option maxHeartbeats 1600000 in
-- Eliminate coefficient equalities before instantiating the localization square.
private theorem proetale_localize_transition
    (X Y : Scheme.{u})
    (BX : ℕ → Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (τX : ∀ k, BX (k + 1) ⟶ BX k)
    (BY : ℕ → Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (τY : ∀ k, BY (k + 1) ⟶ BY k)
    {m n : ℕ} (h : m ≤ n)
    (αX : BX n ⟶ BX m)
    (eX : SemilinearSections.coefficientMap.{u + 1, u, u + 1} (ProEt.topology X) BX τX h = αX)
    (αY : BY n ⟶ BY m)
    (eY : SemilinearSections.coefficientMap.{u + 1, u, u + 1} (ProEt.topology Y) BY τY h = αY)
    (U : SemilinearSections.Systems.{u + 1, u, u + 1} (ProEt.topology Y) BY τY ⥤
      SemilinearSections.Systems.{u + 1, u, u + 1} (ProEt.topology X) BX τX)
    (F₀ : SemilinearSections.Mod.{u + 1, u, u + 1} (ProEt.topology Y) (BY n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (ProEt.topology X) (BX n))
    (F₁ : SemilinearSections.Mod.{u + 1, u, u + 1} (ProEt.topology Y) (BY m) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} (ProEt.topology X) (BX m))
    [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    (a₀ : U ⋙ SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) BX τX n ≅
      SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology Y) BY τY n ⋙ F₀)
    (a₁ : U ⋙ SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) BX τX m ≅
      SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology Y) BY τY m ⋙ F₁)
    (γ : proEtaleRingRestrictScalars αY ⋙ F₀ ≅ F₁ ⋙ proEtaleRingRestrictScalars αX)
    (hord : ∀ N,
      (transportedTransition X BX τX h αX eX).app (U.obj N) ≫
          (proEtaleRingRestrictScalars αX).map (a₁.hom.app N) =
        a₀.hom.app N ≫ F₀.map ((transportedTransition Y BY τY h αY eY).app N) ≫
          γ.hom.app ((SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology Y) BY τY
            m).obj N))
    (M : SemilinearSections.DS.{u + 1, u, u + 1} (ProEt.topology Y) BY τY) :
    (transportedDerivedTransition X BX τX h αX eX).app (U.mapDerivedCategory.obj M) ≫
        (proEtaleRingRestrictScalars αX).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso a₁).hom.app M) =
      (Functor.mapDerivedCategorySquareIso a₀).hom.app M ≫
        F₀.mapDerivedCategory.map ((transportedDerivedTransition Y BY τY h αY eY).app M) ≫
        (Functor.mapDerivedCategorySquareIso γ).hom.app
          ((SemilinearSections.e.{u + 1, u, u + 1} (ProEt.topology Y) BY τY m).obj M) := by
  subst αX αY
  simp only [transportedTransition, transportedDerivedTransition,
    eqToIso_refl, Iso.refl_hom, Functor.whiskerLeft_id', Category.comp_id] at hord ⊢
  have result := localize_transition U
    (SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology Y) BY τY n)
    (SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology Y) BY τY m)
    (SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) BX τX n)
    (SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) BX τX m)
    F₀ F₁
    (SemilinearSections.res.{u + 1, u, u + 1} (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
      (ProEt.topology Y) BY τY h))
    (SemilinearSections.res.{u + 1, u, u + 1} (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
      (ProEt.topology X) BX τX h))
    a₀ a₁ γ
    (SemilinearSections.transition.{u + 1, u, u + 1} (ProEt.topology Y) BY τY h)
    (SemilinearSections.transition.{u + 1, u, u + 1} (ProEt.topology X) BX τX h)
    (SemilinearSections.derivedTransition.{u + 1, u, u + 1} (ProEt.topology Y) BY τY h)
    (SemilinearSections.derivedTransition.{u + 1, u, u + 1} (ProEt.topology X) BX τX h)
    (SemilinearSections.derived_transition_fac.{u + 1, u, u + 1} (ProEt.topology Y) BY τY h)
    (SemilinearSections.derived_transition_fac.{u + 1, u, u + 1} (ProEt.topology X) BX τX h)
    hord M
  run_tac transportInstances `result

end

private abbrev canonicalRestrictionComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingRestrictionPullbackInv f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (by simpa only [proEtaleConstantRingComparison, asIso_hom,
      proEtaleCoefficientInverseImageMap, proEtaleConstantRingMap] using
      (proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))).symm)

private abbrev canonicalDirectComparison {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleRingRestrictionDirectImage f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (by simpa only [proEtaleConstantRingComparison, asIso_hom,
      proEtaleCoefficientInverseImageMap, proEtaleConstantRingMap] using
      (proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))).symm)

private theorem canonicalDirectComparison_apply
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : proEtaleRingModules X (proEtaleConstantRing X B)) (U : Y.ProEtᵒᵖ)
    (x : N.val.obj ((proEtaleBaseChange f).op.obj U)) :
    ((canonicalDirectComparison φ f).hom.app N).val.app U x = x :=
  (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
    f (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (by simpa only [proEtaleConstantRingComparison, asIso_hom,
      proEtaleCoefficientInverseImageMap, proEtaleConstantRingMap] using
      (proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))).symm))).1 N U x

set_option maxHeartbeats 1600000 in
-- Conjugating the ordinary finite units unfolds several module-sheaf functor presentations.
private theorem ordinary_unit_square
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (φY : proEtaleConstantRing Y A ⟶ proEtaleConstantRing Y B)
    (φX : proEtaleConstantRing X A ⟶ proEtaleConstantRing X B)
    (hY : φY = proEtaleConstantRingMap (T := Y) φ)
    (hX : φX = proEtaleConstantRingMap (T := X) φ)
    (Mₙ : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (Mₘ : proEtaleRingModules Y (proEtaleConstantRing Y B))
    (Nₙ : proEtaleRingModules X (proEtaleConstantRing X A))
    (Nₘ : proEtaleRingModules X (proEtaleConstantRing X B))
    (eₙ : Nₙ ≅ (proEtaleConstantRingPullback A f).obj Mₙ)
    (eₘ : Nₘ ≅ (proEtaleConstantRingPullback B f).obj Mₘ)
    (tY : Mₙ ⟶ (SemilinearSections.res.{u + 1, u, u + 1} φY).obj Mₘ)
    (tX : Nₙ ⟶ (SemilinearSections.res.{u + 1, u, u + 1} φX).obj Nₘ)
    (hu : ∀ (U : Y.ProEtᵒᵖ) (x : Mₙ.val.obj U) (y : Mₘ.val.obj U),
      HEq (tY.val.app U x) y →
      HEq ((((proEtaleConstantRingAdjunction A f).homEquiv _ _)
        (eₙ.inv ≫ tX ≫ (SemilinearSections.res.{u + 1, u, u + 1} φX).map eₘ.hom)).val.app U x)
        (((proEtaleConstantRingAdjunction B f).unit.app Mₘ).val.app U y)) :
    tX ≫ (eqToIso (congrArg (fun a ↦ SemilinearSections.res.{u + 1, u, u + 1} a)
        hX)).hom.app Nₘ ≫
        (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ)).map eₘ.hom =
      eₙ.hom ≫ (proEtaleConstantRingPullback A f).map
        (tY ≫ (eqToIso (congrArg
          (fun a ↦ SemilinearSections.res.{u + 1, u, u + 1} a) hY)).hom.app Mₘ) ≫
        (canonicalRestrictionComparison φ f).app Mₘ := by
  subst φY
  subst φX
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Category.comp_id]
  apply (cancel_epi eₙ.inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply ((proEtaleConstantRingAdjunction A f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  have hβ : ((proEtaleConstantRingAdjunction A f).homEquiv _ _)
      ((canonicalRestrictionComparison φ f).app Mₘ) =
      (proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ)).map
        ((proEtaleConstantRingAdjunction B f).unit.app Mₘ) ≫
        (canonicalDirectComparison φ f).hom.app
          ((proEtaleConstantRingPullback B f).obj Mₘ) := by
    dsimp only [canonicalRestrictionComparison, proEtaleRingRestrictionPullbackInv,
      proEtaleRingRestrictionPullbackApp]
    rw [← Functor.map_comp_assoc]
    exact Equiv.apply_symm_apply _ _
  erw [hβ]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  let y : Mₘ.val.obj U := tY.val.app U x
  have hh := hu U x y (HEq.refl _)
  change _ = ((canonicalDirectComparison φ f).hom.app
    ((proEtaleConstantRingPullback B f).obj Mₘ)).val.app U
      (((proEtaleConstantRingAdjunction B f).unit.app Mₘ).val.app U y)
  rw [show ((canonicalDirectComparison φ f).hom.app
      ((proEtaleConstantRingPullback B f).obj Mₘ)).val.app U
        (((proEtaleConstantRingAdjunction B f).unit.app Mₘ).val.app U y) =
      ((proEtaleConstantRingAdjunction B f).unit.app Mₘ).val.app U y from
        canonicalDirectComparison_apply φ f _ _ _]
  exact eq_of_heq hh
private theorem transported_homEquiv
    {C D : Type*} [categoryC : Category C] [categoryD : Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G')
    (s : F ≅ F') (r : G ≅ G')
    (hu : ∀ P, a.unit.app P ≫ G.map (s.hom.app P) ≫ r.hom.app (F'.obj P) =
      b.unit.app P) (P : C) (Q : D) (f : F.obj P ⟶ Q) :
    b.homEquiv P Q (coordinateReduction s f) = a.homEquiv P Q f ≫ r.hom.app Q := by
  dsimp only [coordinateReduction]
  rw [a.homEquiv_unit, b.homEquiv_unit, ← hu P]
  simp only [Functor.map_comp, Category.assoc]
  rw [← r.hom.naturality_assoc (s.inv.app P)]
  rw [← G.map_comp_assoc, Iso.hom_inv_id_app, G.map_id, Category.id_comp]
  rw [r.hom.naturality]


private theorem unique_transpose
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (a : F ⊣ G) (c : F' ⊣ G')
    (e : G ≅ G') (P : C) (Q : D) (t : P ⟶ G.obj Q) :
    c.homEquiv P Q
      (coordinateReduction (a.leftAdjointUniq (c.ofNatIsoRight e.symm))
        ((a.homEquiv P Q).symm t)) = t ≫ e.hom.app Q := by
  let s := a.leftAdjointUniq (c.ofNatIsoRight e.symm)
  have hu (N : C) : a.unit.app N ≫ G.map (s.hom.app N) ≫
      e.hom.app (F'.obj N) = c.unit.app N := by
    rw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
    change (c.unit.app N ≫ e.inv.app _) ≫ e.hom.app _ = c.unit.app N
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have result := transported_homEquiv a c s e hu P Q ((a.homEquiv P Q).symm t)
  simpa only [Equiv.apply_symm_apply] using result

private theorem whisker_comp_app
    {C D F : Type*} [Category C] [Category D] [Category F]
    {U : C ⥤ F} {V : C ⥤ D} {R S : D ⥤ F}
    (a : U ⟶ V ⋙ R) (e : R ⟶ S) (N : C) :
    (a ≫ whiskerLeft V e).app N = a.app N ≫ e.app (V.obj N) := rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section
attribute [local implicit_reducible] rho scalarCoordinates SemilinearSections.reduction
attribute [local irreducible] coordinateReduction
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem scalarCoordinates_eq (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) :
    scalarCoordinates l E b T h =
      ((b.calculus T).scalar h).adjunction.leftAdjointUniq
        ((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := T) (quotientMap l E h))).ofNatIsoRight
          (eqToIso (congrArg (fun a ↦ SemilinearSections.resD a)
            (coefficientMap_eq l E T h))).symm) := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
-- Convert the generic and canonical derived coefficient-category presentations.
private theorem rho_transpose (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E T) :
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotientMap l E h))).homEquiv _ _
      (rho l E b T h M) =
    (SemilinearSections.derivedTransition.{u + 1, u, u + 1} (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app M ≫
      (eqToIso (congrArg (fun a ↦ SemilinearSections.resD a)
        (coefficientMap_eq l E T h))).hom.app ((SpTowerShriek.Ev l E T m).obj M) := by
  unfold rho
  rw [scalarCoordinates_eq]
  dsimp only [SemilinearSections.reduction]
  have result := unique_transpose ((b.calculus T).scalar h).adjunction
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotientMap l E h)))
    (eqToIso (congrArg (fun a ↦ SemilinearSections.resD a)
      (coefficientMap_eq l E T h)))
    ((SpTowerShriek.Ev l E T n).obj M) ((SpTowerShriek.Ev l E T m).obj M)
    ((SemilinearSections.derivedTransition.{u + 1, u, u + 1} (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app M)
  run_tac transportInstances `result

end

private def constantTransition (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SpTowerShriek.ev l E T n ⟶ SpTowerShriek.ev l E T m ⋙
      proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) (quotientMap l E h)) :=
  SemilinearSections.transition (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) h ≫
    whiskerLeft (SpTowerShriek.ev l E T m)
      (eqToIso (congrArg (fun a ↦ SemilinearSections.res a)
        (coefficientMap_eq l E T h))).hom

private def constantDerivedTransition (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    SpTowerShriek.Ev l E T n ⟶ SpTowerShriek.Ev l E T m ⋙
      (proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := T) (quotientMap l E h))).mapDerivedCategory :=
  SemilinearSections.derivedTransition (ProEt.topology T) (SpTowerShriek.B l E T)
      (SpTowerShriek.tau l E T) h ≫
    whiskerLeft (SpTowerShriek.Ev l E T m)
      (eqToIso (congrArg (fun a ↦ SemilinearSections.resD a)
        (coefficientMap_eq l E T h))).hom

attribute [local implicit_reducible] constantTransition constantDerivedTransition

private theorem constantDerivedTransition_app (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (N : SpTowerShriek.D l E T) :
    (constantDerivedTransition l E T h).app N =
      (SemilinearSections.derivedTransition.{u + 1, u, u + 1} (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h).app N ≫
      (eqToIso (congrArg (fun a ↦ SemilinearSections.resD a)
        (coefficientMap_eq l E T h))).hom.app ((SpTowerShriek.Ev l E T m).obj N) := by
  unfold constantDerivedTransition
  have result := whisker_comp_app
    (SemilinearSections.derivedTransition (ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)
    (eqToIso (congrArg (fun a ↦ SemilinearSections.resD a)
      (coefficientMap_eq l E T h))).hom N
  run_tac transportInstances `result


private theorem ordinary_restriction_transition (b : SpTowerShriek.Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.S l E Y) :
    (constantTransition l E X h).app (g.pull.obj M) ≫
      (proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := X) (quotientMap l E h))).map
          ((g.ordinaryPullEvaluation m).hom.app M) =
    (g.ordinaryPullEvaluation n).hom.app M ≫
      (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).map
        ((constantTransition l E Y h).app M) ≫
      (canonicalRestrictionComparison (quotientMap l E h) f).app
        ((SpTowerShriek.ev l E Y m).obj M) := by
  have hu := g.ordinaryUnitTransition
  unfold SpTowerShriek.OrdinaryUnitTransition SpTowerShriek.OrdinaryUnitTransitionModel at hu
  have result := ordinary_unit_square (quotientMap l E h) f
    (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (ProEt.topology Y)
      (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) h)
    (SemilinearSections.coefficientMap.{u + 1, u, u + 1} (ProEt.topology X)
      (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h)
    (coefficientMap_eq l E Y h) (coefficientMap_eq l E X h)
    ((SpTowerShriek.ev l E Y n).obj M) ((SpTowerShriek.ev l E Y m).obj M)
    ((SpTowerShriek.ev l E X n).obj (g.pull.obj M))
    ((SpTowerShriek.ev l E X m).obj (g.pull.obj M))
    ((g.ordinaryPullEvaluation n).app M) ((g.ordinaryPullEvaluation m).app M)
    ((SemilinearSections.transition.{u + 1, u, u + 1} (ProEt.topology Y)
      (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) h).app M)
    ((SemilinearSections.transition.{u + 1, u, u + 1} (ProEt.topology X)
      (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app (g.pull.obj M))
    (hu M h)
  exact result

private def canonicalRestrictionIso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := Y) φ) ⋙
        proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback B f ⋙
        proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := X) φ) := by
  have : IsIso (canonicalRestrictionComparison φ f) :=
    proEtaleRingRestrictionPullbackInv_isIso _ _ _ _ _ _ _ _ _ _
  exact asIso (canonicalRestrictionComparison φ f)

section

set_option maxHeartbeats 1600000 in
-- Compare the localized square with the specified evaluation coordinates.
private theorem derived_restriction_transition (b : SpTowerShriek.Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E Y) :
    (constantDerivedTransition l E X h).app ((SpTowerShriek.pull l E b g).obj M) ≫
      (proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := X) (quotientMap l E h))).mapDerivedCategory.map
          ((g.pullEvaluation m).hom.app M) =
    (g.pullEvaluation n).hom.app M ≫
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).map
        ((constantDerivedTransition l E Y h).app M) ≫
      (Functor.mapDerivedCategorySquareIso
        (canonicalRestrictionIso (quotientMap l E h) f)).hom.app
        ((SpTowerShriek.Ev l E Y m).obj M) := by
  rw [SpTowerShriek.pull_evaluation_model l E b g n,
    SpTowerShriek.pull_evaluation_model l E b g m]
  have result := proetale_localize_transition X Y
    (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X)
    (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y) h
    (proEtaleConstantRingMap (T := X) (quotientMap l E h)) (coefficientMap_eq l E X h)
    (proEtaleConstantRingMap (T := Y) (quotientMap l E h)) (coefficientMap_eq l E Y h)
    g.pull
    (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f)
    (proEtaleConstantRingPullback (SpTowerShriek.R l E m) f)
    (g.ordinaryPullEvaluation n) (g.ordinaryPullEvaluation m)
    (canonicalRestrictionIso (quotientMap l E h) f)
    (ordinary_restriction_transition l E b g h) M
  unfold transportedDerivedTransition at result
  unfold constantDerivedTransition
  run_tac transportInstances `result

end

private theorem localized_symm_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (Functor.mapDerivedCategoryNatIso e.symm).inv =
      (Functor.mapDerivedCategoryNatIso e).hom := by
  exact (Functor.mapDerivedCategoryNatIso_symm e.symm).symm

private theorem canonicalComparison_transpose
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (P : proEtaleDerivedCategory Y A) :
    (proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := X) φ)).homEquiv _ _
      ((directImageScalarPullbackIso φ f).inv.app P) =
      (proEtaleConstantRingDerivedPullback A f).map
        ((proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := Y) φ)).unit.app P) ≫
        (Functor.mapDerivedCategorySquareIso (canonicalRestrictionIso φ f)).hom.app
          ((scalarExtensionFunctor φ Y).obj P) := by
  let a := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ)
  let b := proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ)
  let β := proEtaleRingRestrictionDerivedPullback f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (by simpa only [proEtaleConstantRingComparison, asIso_hom,
      proEtaleCoefficientInverseImageMap, proEtaleConstantRingMap] using
      (proEtaleConstantInverseImageMap_naturality f
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} φ))).symm)
  have hβ : (Functor.mapDerivedCategorySquareIso (canonicalRestrictionIso φ f)).hom =
      β.inv := by
    simp only [β, Functor.mapDerivedCategorySquareIso, canonicalRestrictionIso,
      proEtaleRingRestrictionDerivedPullback, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, localized_symm_inv, Category.assoc]
  rw [hβ]
  change b.homEquiv _ _ (((mateEquiv a b).symm
    (TwoSquare.mk _ _ _ _ β.inv)).natTrans.app P) = _
  rw [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ β.inv) P).symm

private theorem canonical_scalar_transition
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {P₀ : proEtaleDerivedCategory Y A} {P₁ : proEtaleDerivedCategory Y B}
    {Q₀ : proEtaleDerivedCategory X A} {Q₁ : proEtaleDerivedCategory X B}
    (a₀ : Q₀ ⟶ (proEtaleConstantRingDerivedPullback A f).obj P₀)
    (a₁ : Q₁ ⟶ (proEtaleConstantRingDerivedPullback B f).obj P₁)
    (τ : P₀ ⟶ ((proEtaleRingRestrictScalars
      (proEtaleConstantRingMap (T := Y) φ)).mapDerivedCategory).obj P₁)
    (σ : Q₀ ⟶ ((proEtaleRingRestrictScalars
      (proEtaleConstantRingMap (T := X) φ)).mapDerivedCategory).obj Q₁)
    (ht : σ ≫ (proEtaleRingRestrictScalars
        (proEtaleConstantRingMap (T := X) φ)).mapDerivedCategory.map a₁ =
      a₀ ≫ (proEtaleConstantRingDerivedPullback A f).map τ ≫
        (Functor.mapDerivedCategorySquareIso (canonicalRestrictionIso φ f)).hom.app P₁) :
    ((proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := X) φ)).homEquiv Q₀ Q₁).symm σ ≫ a₁ =
      (scalarExtensionFunctor φ X).map a₀ ≫ (directImageScalarPullbackIso φ f).inv.app P₀ ≫
        (proEtaleConstantRingDerivedPullback B f).map
          (((proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := Y) φ)).homEquiv P₀ P₁).symm τ) := by
  exact scalar_transition
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Y) φ))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
    (directImageScalarPullbackIso φ f)
    (Functor.mapDerivedCategorySquareIso (canonicalRestrictionIso φ f))
    (canonicalComparison_transpose φ f) a₀ a₁ τ σ ht

private theorem constantDerivedTransition_transpose (b : SpTowerShriek.Base l E)
    (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) (N : SpTowerShriek.D l E T) :
    ((proEtaleRingDerivedExtensionAdjunction
      (proEtaleConstantRingMap (T := T) (quotientMap l E h))).homEquiv _ _).symm
      ((constantDerivedTransition l E T h).app N) = rho l E b T h N := by
  apply ((proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := T) (quotientMap l E h))).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  exact (constantDerivedTransition_app l E T h N).trans (rho_transpose l E b T h N).symm


set_option maxHeartbeats 1600000 in
-- The final scalar transpose compares the two published finite-level category models.
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Inverse image carries the actual reduction maps through the canonical scalar comparison.
Source: Zheng 4.1 and blueprint integral direct-image proof (1).
Proof: the specified finite-unit transition equation identifies the ordinary restriction
square with the identity-on-sections canonical comparison. Localize this exact square.
Adjunction uniqueness identifies rho with its canonical scalar transpose, and transposing
the localized square gives the displayed equation.
(blueprint: lem-sp-normalized-pull-transition). -/
theorem normalized_pull_transition (b : SpTowerShriek.Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E Y) :
    rho l E b X h ((SpTowerShriek.pull l E b g).obj M) ≫
        (g.pullEvaluation m).hom.app M =
      (scalarExtensionFunctor (quotientMap l E h) X).map
          ((g.pullEvaluation n).hom.app M) ≫
        (directImageScalarPullbackIso (quotientMap l E h) f).inv.app
          ((SpTowerShriek.Ev l E Y n).obj M) ≫
        (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E m) f).map
          (rho l E b Y h M) := by
  have ht := derived_restriction_transition l E b g h M
  have hh := canonical_scalar_transition (quotientMap l E h) f
    ((g.pullEvaluation n).hom.app M) ((g.pullEvaluation m).hom.app M)
    ((constantDerivedTransition l E Y h).app M)
    ((constantDerivedTransition l E X h).app ((SpTowerShriek.pull l E b g).obj M))
    ht
  dsimp only [Functor.comp_obj] at hh
  -- Substitute the two coordinates by congruence, keeping derived-functor motives small.
  have hx := constantDerivedTransition_transpose l E b X h
    ((SpTowerShriek.pull l E b g).obj M)
  have hy := constantDerivedTransition_transpose l E b Y h M
  exact (congrArg (fun z ↦ z ≫ (g.pullEvaluation m).hom.app M) hx.symm).trans
    (hh.trans (congrArg (fun z ↦
      (scalarExtensionFunctor (quotientMap l E h) X).map
          ((g.pullEvaluation n).hom.app M) ≫
        (directImageScalarPullbackIso (quotientMap l E h) f).inv.app
          ((SpTowerShriek.Ev l E Y n).obj M) ≫
        (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E m) f).map z) hy))

end AlgebraicGeometry.ProEtale.SpShriekTransition

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
