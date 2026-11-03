/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChartComparisons.GeneralChartComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChartFactors.ChartDncVectorFactorData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Logic.Function.Basic
import all WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Tensor.TensorMateEtalePrecomp
import all WeilConjectures.AlgebraicGeometry.EtaleSupportExchange.EtaleSupportExchangeRightMate

/-! # Standing exceptional composition and normalized etale locality

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Step 3, composition of adjunctions.
(blueprint: lem-pur-chart-exceptional-counit-equation).

The canonical uniqueness-of-adjoints comparison is directed from the diagonal
omega object to the standing exceptional value. Its inverse identifies the standing
value with omega in the equation below.
-/

@[expose] public section

/- The source definition caches typeclass proofs inside derived-category data. A reflexivity
check across those cached proofs can unfold the entire compositor. This local automation
instead builds explicit heterogeneous congruences, with proof irrelevance at proof arguments;
its output is an ordinary proof term checked by the kernel. -/
universe v w

private theorem chartPiHEq {α β : Sort v} {F : α → Sort w} {G : β → Sort w}
    (h : α = β) (hFG : HEq F G) : HEq ((x : α) → F x) ((x : β) → G x) := by
  cases h
  cases hFG
  rfl

private theorem chartInferInstanceHEq {α : Sort v} (a : α) :
    HEq (@inferInstance α a) a := by
  rfl

private theorem chartFullSubcategoryObjHEq {C : Type v} [CategoryTheory.Category.{w} C]
    {P : CategoryTheory.ObjectProperty C}
    (X : C) (hX : P X) :
    HEq ((⟨X, hX⟩ : P.FullSubcategory).obj) X := by
  rfl

meta section

private def chartInstanceNormalize (e : Lean.Expr) (fuel : Nat) : Lean.Meta.MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e := e.consumeMData
    if e.isAppOf ``AlgebraicGeometry.Etale.cartierAbelianEtale ||
        e.isAppOf ``AlgebraicGeometry.Etale.cartierAbelianPro ||
        e.isAppOf ``WeilConjectures.PurityFiniteSetting.chartCoefficientUnit ||
        e.isAppOf ``WeilConjectures.PurityFiniteSetting.diagonalOrdinaryDualizing ||
        e.isAppOf ``WeilConjectures.PurityFiniteSetting.ChartComparisons.composition ||
        e.isAppOf ``AlgebraicGeometry.ProEtale.standingExceptionalComposition then
      if let some e ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e) then
        return ← chartInstanceNormalize e fuel
    match e with
    | .letE _ _ v b _ => chartInstanceNormalize (b.instantiate1 v) fuel
    | .fvar id =>
      match (← Lean.getLCtx).get! id |>.value? (allowNondep := true) with
      | some v =>
        modifyThe Lean.Meta.State fun s ↦
          { s with zetaDeltaFVarIds := s.zetaDeltaFVarIds.insert id }
        chartInstanceNormalize v fuel
      | none => return e
    | .app f a =>
      let f ← chartInstanceNormalize f fuel
      let b := (Lean.mkApp f a).headBeta
      if b != e then chartInstanceNormalize b fuel else return e
    | _ => return e

private def chartInstanceHEq (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
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
      let a ← chartInstanceNormalize a 100
      let b ← chartInstanceNormalize b 100
      if a == b then return ← Lean.Meta.mkHEqRefl a
      if a.isAppOf ``inferInstance then
        let x := a.getAppArgs.back!
        let h ← Lean.Meta.mkAppM ``chartInferInstanceHEq #[x]
        let h' ← chartInstanceHEq cache x b fuel
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      if b.isAppOf ``inferInstance then
        let x := b.getAppArgs.back!
        let h ← chartInstanceHEq cache a x fuel
        let h' ← Lean.Meta.mkAppM ``chartInferInstanceHEq #[x]
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
        let value ← chartInstanceNormalize value 100
        unless value.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory.mk do return none
        let args := value.getAppArgs
        let x := args[args.size - 2]!
        let h ← Lean.Meta.mkAppM ``chartFullSubcategoryObjHEq #[x, args.back!]
        return some (x, h)
      if let some (x, h) ← project a then
        let h' ← chartInstanceHEq cache x b fuel
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      if let some (x, h') ← project b then
        let h ← chartInstanceHEq cache a x fuel
        let h' ← Lean.Meta.mkAppM ``HEq.symm #[h']
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      match a, b with
      | .lam _ ta _ _, .lam _ tb _ _ =>
        let hdom ← Lean.Meta.mkAppM ``eq_of_heq #[← chartInstanceHEq cache ta tb fuel]
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
            c.mvarId.assign (← chartInstanceHEq cache args[1]! args[3]! fuel)
        return ← Lean.instantiateMVars g
      | .forallE n ta ab bi, .forallE n' tb bb bi' =>
        let hdom ← Lean.Meta.mkAppM ``eq_of_heq #[← chartInstanceHEq cache ta tb fuel]
        let hf ← chartInstanceHEq cache (.lam n ta ab bi) (.lam n' tb bb bi') fuel
        return ← Lean.Meta.mkAppM ``chartPiHEq #[hdom, hf]
      | _, _ => pure ()
      let af := a.getAppFn
      let bf := b.getAppFn
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      let sameHead ← match af, bf with
        | .const n _, .const m _ =>
          if n == m then Lean.Meta.isDefEq af bf else pure false
        | _, _ => pure (af == bf)
      if sameHead && aa.size == ba.size && !aa.isEmpty then
        let ct ← Lean.Meta.mkHCongrWithArity af aa.size
        let mut args := #[]
        for i in [:aa.size] do
          let h ← chartInstanceHEq cache aa[i]! ba[i]! fuel
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

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local irreducible] ProEtale.originCompositionAmbient
  ProEtale.fixedCompactSupportComparisonIso ProEtale.compactSupportSiteComparison
  Etale.unboundedEtaleLowerShriekCompIso Etale.rightDerivedLowerShriekPlusCompIso
  Etale.rightDerivedUpperShriekAdjunction

namespace AlgebraicGeometry.ProEtale

private def normalizedStandingAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [CompactSpace Y] :
    FixedComparisonClassAdjunction A f (HasCompactification.compactification f)
      (Etale.rightDerivedUpperShriek A f) (Etale.rightDerivedUpperShriekAdjunction A f)
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X)
      _root_.DerivedCategory.TStructure.t.plus :=
  Classical.choice (nonempty_fixedComparisonClassAdjunction_of_boundedBelow A
    (HasCompactification.compactification f) (Etale.rightDerivedUpperShriek A f)
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (fun _ hL ↦ plus_etaleRightDerivedUpperShriek_obj f hL))

attribute [local irreducible] normalizedStandingAdjunction

private theorem standingHom_eq_normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [CompactSpace Y]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (a : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K ⟶ L) :
    standingExceptionalHomEquiv A f hK hL a =
      (normalizedStandingAdjunction A f).homEquiv
        (HasCompactification.compactification f) K hK L hL a := by
  let D := normalizedStandingAdjunction A f
  let K' := Classical.choose hK
  let hK' := (Classical.choose_spec hK).1
  let e := Classical.choice (Classical.choose_spec hK).2
  let hνK' := DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hK'
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let ν := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let s := (fixedCompactSupportComparisonIso A
    (HasCompactification.compactification f)).app ⟨K', hK'⟩
  let adjν := derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y
  let b := (adjν.homEquiv _ L) (s.inv ≫ F.map e.hom ≫ a)
  have hn := D.homEquiv_normalized ⟨K', hK'⟩ hνK' L hL b
  have hl := D.naturality_left (HasCompactification.compactification f)
    (ν.obj K') K hνK' hK L hL e.hom a
  have hb : s.hom ≫ (adjν.homEquiv _ L).symm b = F.map e.hom ≫ a := by
    simp only [b, Equiv.symm_apply_apply, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  change D.homEquiv (HasCompactification.compactification f) (ν.obj K') hνK' L hL
      (s.hom ≫ (adjν.homEquiv _ L).symm b) =
    ν.map ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ _ b) at hn
  erw [hb] at hn
  erw [hl] at hn
  change e.inv ≫ ν.map ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ _ b) = _
  erw [← hn]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

attribute [local irreducible] standingExceptionalHomEquiv

private theorem standingHom_left (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [CompactSpace Y]
    {K K' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    (hK' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K')
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (a : K ⟶ K') (b : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K' ⟶ L) :
    standingExceptionalHomEquiv A f hK hL
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map a ≫ b) =
      a ≫ standingExceptionalHomEquiv A f hK' hL b := by
  erw [standingHom_eq_normalized, standingHom_eq_normalized]
  exact (normalizedStandingAdjunction A f).naturality_left
    (HasCompactification.compactification f) K K' hK hK' L hL a b

private theorem standingHom_right (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [CompactSpace Y]
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    {L L' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hL' : _root_.DerivedCategory.TStructure.t.plus L')
    (a : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K ⟶ L) (b : L ⟶ L') :
    standingExceptionalHomEquiv A f hK hL' (a ≫ b) =
      standingExceptionalHomEquiv A f hK hL a ≫ (rightDerivedUpperShriek A f).map b := by
  erw [standingHom_eq_normalized, standingHom_eq_normalized]
  exact (normalizedStandingAdjunction A f).naturality_right
    (HasCompactification.compactification f) K hK L L' hL hL' a b

private def ordinaryStandingComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hL : _root_.DerivedCategory.TStructure.t.plus L) :
    (rightDerivedUpperShriek A f).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L) ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
        ((Etale.rightDerivedUpperShriek A f).obj L) :=
  letI := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) Y L hL
  (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
    ((Etale.rightDerivedUpperShriek A f).mapIso
      (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app L)).symm)

attribute [local irreducible] ordinaryStandingComparison

private theorem standingHom_image (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [CompactSpace Y]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (a : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K.obj ⟶ L.obj) :
    standingExceptionalHomEquiv A f
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property)
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property).plus
        ((fixedCompactSupportComparisonIso A
          (HasCompactification.compactification f)).hom.app K ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map a) ≫
        (ordinaryStandingComparison A f L.obj L.property).hom =
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ _ a) := by
  let νY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let adjν := derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y
  let adj := Etale.rightDerivedUpperShriekAdjunction A f
  have ht : adjν.homEquiv _ _ (νY.map a) = a ≫ adjν.unit.app L.obj := by
    erw [adjν.homEquiv_unit]
    exact adjν.unit_naturality a
  erw [standingHom_eq_normalized]
  have hn := (normalizedStandingAdjunction A f).homEquiv_normalized K
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property) (νY.obj L.obj)
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property).plus
    (adjν.homEquiv _ _ (νY.map a))
  erw [Equiv.symm_apply_apply] at hn
  erw [hn, ht, adj.homEquiv_naturality_right]
  simp [ordinaryStandingComparison, ← Functor.map_comp]
  rfl

private theorem originComposition_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)] :
    Functor.whiskerLeft (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
        (originCompositionAmbient A f g).hom = (originCompositionModel A f g).hom := by
  let H := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
  have ho : Functor.whiskerRight (originComposition A f g).hom
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι =
      (originCompositionAmbient A f g).hom :=
    (H.whiskeringRight _).map_preimage
      (X := originCompactSupport A f ⋙ originCompactSupport A g)
      (Y := originCompactSupport A (f ≫ g)) (originCompositionAmbient A f g).hom
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  exact (congrArg (Functor.whiskerLeft Φ) ho).symm.trans (originComposition_model A f g)

private theorem component_heq {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y) :
    HEq (α.app X) (α.app Y) := by
  cases h
  rfl

private theorem originComposition_at_image
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (α : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⟶
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (hα : α = (originCompositionAmbient A f g).hom)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    α.app
        ⟨(comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj,
          DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property⟩ =
      (originCompositionModel A f g).hom.app K := by
  let Φ := comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X
  let J : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory :=
    ⟨(comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj,
      DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property⟩
  have hk : Φ.obj K = J := rfl
  have hw : Functor.whiskerLeft Φ α = (originCompositionModel A f g).hom :=
    (congrArg (Functor.whiskerLeft Φ) hα).trans (originComposition_restriction A f g)
  have h : α.app (Φ.obj K) = (originCompositionModel A f g).hom.app K :=
    (Functor.whiskerLeft_app Φ α K).symm.trans (congr_app hw K)
  have hp : α.app J = (originCompositionModel A f g).hom.app K :=
    eq_of_heq ((component_heq α hk).symm.trans (heq_of_eq h))
  exact hp

private theorem fixedComparison_hom_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (fixedCompactSupportComparisonIso A c).hom.app K =
      (compactSupportSiteComparison A c).hom.app K :=
  congrArg (fun i ↦ i.hom.app K) (compactSupportComparisonNormalization A c)

private theorem originCompositionModel_image
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let hF := _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).app K)
      ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K).property
    (originCompositionModel A f g).hom.app K ≫
      (compactSupportSiteComparison A
        (HasCompactification.compactification (f ≫ g))).hom.app K =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          ((compactSupportSiteComparison A
            (HasCompactification.compactification f)).hom.app K) ≫
        (compactSupportSiteComparison A
          (HasCompactification.compactification g)).hom.app
            ⟨(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K.obj, hF⟩ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
          ((Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app K.obj) := by
  dsimp only
  let νZ := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
  let cF := (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).app K
  let KF := (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K
  let hF := _root_.DerivedCategory.TStructure.t.plus.prop_of_iso cF KF.property
  let K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K.obj, hF⟩
  let a : K' ⟶ KF := ObjectProperty.homMk cF.inv
  have hn := (compactSupportSiteComparison A
    (HasCompactification.compactification g)).hom.naturality a
  have hp := Etale.unboundedEtaleCompactSupport_composition_plus A f g K
  have hp' :
      (Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).inv.app KF ≫
        DerivedCategory.Plus.ι.map
          ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app K) ≫
        (Etale.rightDerivedLowerShriekPlusCompatibility
          (ModuleCat.{u + 1} A) (f ≫ g)).hom.app K =
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map cF.hom ≫
        (Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app K.obj := by
    erw [hp, Iso.inv_hom_id_app_assoc]
    rfl
  simp only [originCompositionModel, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [← νZ.map_comp_assoc, ← νZ.map_comp]
  simp only [Category.assoc]
  erw [hp']
  simp only [νZ.map_comp]
  erw [reassoc_of% hn]
  let G := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
  let sf := (compactSupportSiteComparison A
    (HasCompactification.compactification f)).hom.app K
  let sg := (compactSupportSiteComparison A
    (HasCompactification.compactification g)).hom.app K'
  let c := (Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app K.obj
  change F.map sf ≫ sg ≫ νZ.map (G.map cF.inv) ≫ νZ.map (G.map cF.hom) ≫
      νZ.map c = F.map sf ≫ sg ≫ νZ.map c
  have hc : νZ.map (G.map cF.inv) ≫ νZ.map (G.map cF.hom) ≫ νZ.map c =
      νZ.map c := by
    erw [← νZ.map_comp_assoc, ← G.map_comp, cF.inv_hom_id,
      G.map_id, νZ.map_id, Category.id_comp]
  exact congrArg (fun t ↦ F.map sf ≫ sg ≫ t) hc

private theorem transport_compositor_image
    {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {U V : C} {W T Q : D}
    (a m : G.obj U ⟶ T) (f f' : U ⟶ V)
    (g g' : G.obj V ⟶ W) (h h' : T ⟶ Q) (c : W ⟶ Q)
    (ha : a = m) (hf : f = f') (hg : g = g') (hh : h = h')
    (hm : m ≫ h' = G.map f' ≫ g' ≫ c) :
    a ≫ h = G.map f ≫ g ≫ c := by
  calc
    _ = m ≫ h' := congrArg₂ (fun x y ↦ x ≫ y) ha hh
    _ = G.map f' ≫ g' ≫ c := hm
    _ = _ := congrArg₂ (fun x y ↦ G.map x ≫ y ≫ c) hf.symm hg.symm

private theorem originComposition_image
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (α : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⟶
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (hα : α = (originCompositionAmbient A f g).hom)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let hK := DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property
    let hF := _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).app K)
      ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K).property
    α.app
        ⟨(comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj, hK⟩ ≫
      (fixedCompactSupportComparisonIso A
        (HasCompactification.compactification (f ≫ g))).hom.app K =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          ((fixedCompactSupportComparisonIso A
            (HasCompactification.compactification f)).hom.app K) ≫
        (fixedCompactSupportComparisonIso A
          (HasCompactification.compactification g)).hom.app
            ⟨(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K.obj, hF⟩ ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
          ((Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app K.obj) := by
  dsimp only
  let hF := _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    ((Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).app K)
    ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K).property
  let K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K.obj, hF⟩
  exact transport_compositor_image (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (U := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj))
    (V := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K.obj))
    (W := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K.obj)))
    (T := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj))
    (Q := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj K.obj))
    (α.app
      ⟨(comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj,
        DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj K.property⟩)
    ((originCompositionModel A f g).hom.app K)
    ((fixedCompactSupportComparisonIso A
      (HasCompactification.compactification f)).hom.app K)
    ((compactSupportSiteComparison A
      (HasCompactification.compactification f)).hom.app K)
    ((fixedCompactSupportComparisonIso A
      (HasCompactification.compactification g)).hom.app K')
    ((compactSupportSiteComparison A
      (HasCompactification.compactification g)).hom.app K')
    ((fixedCompactSupportComparisonIso A
      (HasCompactification.compactification (f ≫ g))).hom.app K)
    ((compactSupportSiteComparison A
      (HasCompactification.compactification (f ≫ g))).hom.app K)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
      ((Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app K.obj))
    (originComposition_at_image A f g α hα K)
    (fixedComparison_hom_app A (HasCompactification.compactification f) K)
    (fixedComparison_hom_app A (HasCompactification.compactification g) K')
    (fixedComparison_hom_app A (HasCompactification.compactification (f ≫ g)) K)
    (originCompositionModel_image A f g K)

private theorem counit_transpose {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (L : D) :
    adj.homEquiv (G.obj L) L (adj.counit.app L) = 𝟙 (G.obj L) := by
  rw [← adj.homEquiv_symm_id]
  exact Equiv.apply_symm_apply _ _

private theorem comparison_counit {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {K J : C} {L : D}
    (φ : (F.obj K ⟶ L) ≃ (K ⟶ K))
    (ψ : (F.obj J ⟶ L) ≃ (J ⟶ K)) (j : K ≅ J) (b : F.obj J ⟶ L)
    (hn : ∀ a : F.obj K ⟶ L, ψ (F.map j.inv ≫ a) = j.inv ≫ φ a)
    (hb : ψ b ≫ j.hom = 𝟙 J) :
    F.map j.inv ≫ φ.symm (𝟙 K) = b := by
  apply ψ.injective
  have hφ : φ (φ.symm (𝟙 K)) = 𝟙 K := φ.apply_symm_apply (𝟙 K)
  have hψ : ψ b = j.inv := by
    apply (cancel_mono j.hom).1
    exact hb.trans j.inv_hom_id.symm
  calc
    _ = j.inv ≫ φ (φ.symm (𝟙 K)) := hn _
    _ = j.inv ≫ 𝟙 K := congrArg (fun a ↦ j.inv ≫ a) hφ
    _ = j.inv := Category.comp_id _
    _ = ψ b := hψ.symm

private theorem iterated_transpose_mate
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ E} {S : E ⥤ D}
    {H : C ⥤ E} {T : E ⥤ C}
    (adjf : F ⊣ R) (adjg : G ⊣ S) (adjh : H ⊣ T)
    (c : F ⋙ G ≅ H) (L : E) :
    adjf.homEquiv _ _
        (adjg.homEquiv _ _ (c.hom.app (T.obj L) ≫ adjh.counit.app L)) =
      (conjugateIsoEquiv adjh (adjf.comp adjg) c).hom.app L := by
  calc
    _ = (adjf.comp adjg).homEquiv (T.obj L) L
        (c.hom.app (T.obj L) ≫ adjh.counit.app L) :=
      (congrArg (fun e ↦ (e (T.obj L) L)
        (c.hom.app (T.obj L) ≫ adjh.counit.app L))
          (Adjunction.comp_homEquiv adjf adjg)).symm
    _ = _ := by
      apply ((adjf.comp adjg).homEquiv (T.obj L) L).symm.injective
      rw [Equiv.symm_apply_apply]
      exact (conjugateEquiv_counit adjh (adjf.comp adjg) c.hom L).symm

private theorem cancel_inv_source
    {C : Type*} [Category* C] {X Y Z : C} (j : X ≅ Y)
    (a : X ⟶ Z) (b : Y ⟶ Z) (h : j.inv ≫ a = b) : a = j.hom ≫ b := by
  rw [← h, ← Category.assoc, j.hom_inv_id, Category.id_comp]

private theorem standingCounit_image
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let νY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
    let hL := (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property).plus
    let K := (rightDerivedUpperShriek A f).obj (νY.obj L.obj)
    let hK := plusEtaleOrigin_rightDerivedUpperShriek_obj f hL
    let J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      ⟨(Etale.rightDerivedUpperShriek A f).obj L.obj,
        Etale.plus_rightDerivedUpperShriek_obj A f L.obj L.property⟩
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
        (ordinaryStandingComparison A f L.obj L.property).inv ≫
      (standingExceptionalHomEquiv A f hK hL).symm (𝟙 K) =
      (fixedCompactSupportComparisonIso A
        (HasCompactification.compactification f)).hom.app J ≫
        νY.map ((Etale.rightDerivedUpperShriekAdjunction A f).counit.app L.obj) := by
  let νX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let νY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let hL := (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property).plus
  let K := (rightDerivedUpperShriek A f).obj (νY.obj L.obj)
  let hK := plusEtaleOrigin_rightDerivedUpperShriek_obj f hL
  let J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(Etale.rightDerivedUpperShriek A f).obj L.obj,
      Etale.plus_rightDerivedUpperShriek_obj A f L.obj L.property⟩
  let hJ := DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj J.property
  let j := ordinaryStandingComparison A f L.obj L.property
  let adj := Etale.rightDerivedUpperShriekAdjunction A f
  let counit : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj J.obj ⟶
      L.obj := adj.counit.app L.obj
  let beta := (fixedCompactSupportComparisonIso A
    (HasCompactification.compactification f)).hom.app J ≫ νY.map counit
  have hb0 := standingHom_image A f J L counit
  have he := counit_transpose adj L.obj
  have hid : νX.map (adj.homEquiv _ _ counit) = 𝟙 (νX.obj J.obj) :=
    (congrArg (fun a ↦ νX.map a) he).trans
      (CategoryTheory.Functor.map_id νX J.obj)
  have hb0' : standingExceptionalHomEquiv A f hJ hL beta ≫ j.hom =
      𝟙 (νX.obj J.obj) := hb0.trans hid
  exact comparison_counit (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (K := K) (J := νX.obj J.obj) (L := νY.obj L.obj)
    (standingExceptionalHomEquiv A f hK hL)
    (standingExceptionalHomEquiv A f hJ hL) j beta
    (fun a ↦ standingHom_left A f hJ hK hL j.inv a) hb0'

private theorem standingTranspose_source
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    {K₀ K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (hK₀ : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K₀)
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X K)
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L) (a : K₀ ⟶ K)
    (α : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⟶
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (cb : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj K ⟶ L)
    (beta : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj K₀ ⟶ L)
    (hb : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map a ≫ cb = beta) :
      a ≫ standingExceptionalHomEquiv A f hK (plus_rightDerivedUpperShriek_obj g hL)
        (standingExceptionalHomEquiv A g (hK.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨K, hK⟩ ≫ cb)) =
      standingExceptionalHomEquiv A f hK₀ (plus_rightDerivedUpperShriek_obj g hL)
        (standingExceptionalHomEquiv A g (hK₀.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨K₀, hK₀⟩ ≫ beta)) := by
  have hn := α.naturality (ObjectProperty.homMk a :
    (⟨K₀, hK₀⟩ :
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) ⟶ ⟨K, hK⟩)
  have hn' : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map a) ≫
          α.app ⟨K, hK⟩ =
      α.app ⟨K₀, hK₀⟩ ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map a := by
    dsimp only [Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_map,
      ObjectProperty.ι_obj, ObjectProperty.homMk_hom] at hn
    exact hn
  have hsource :
      a ≫ standingExceptionalHomEquiv A f hK (plus_rightDerivedUpperShriek_obj g hL)
        (standingExceptionalHomEquiv A g (hK.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨K, hK⟩ ≫ cb)) =
      standingExceptionalHomEquiv A f hK₀ (plus_rightDerivedUpperShriek_obj g hL)
        (standingExceptionalHomEquiv A g (hK₀.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨K₀, hK₀⟩ ≫ beta)) := by
    have hf := standingHom_left A f hK₀ hK (plus_rightDerivedUpperShriek_obj g hL)
      a (standingExceptionalHomEquiv A g (hK.rightDerivedLowerShriek_obj f) hL
        (α.app ⟨K, hK⟩ ≫ cb))
    have hl := standingHom_left A g (hK₀.rightDerivedLowerShriek_obj f)
      (hK.rightDerivedLowerShriek_obj f) hL
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map a)
      (α.app ⟨K, hK⟩ ≫ cb)
    have hncb : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map a) ≫
            α.app ⟨K, hK⟩ ≫ cb =
        α.app ⟨K₀, hK₀⟩ ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map a ≫ cb := by
      simpa only [Category.assoc] using congrArg (fun a ↦ a ≫ cb) hn'
    have hβ := hncb.trans (congrArg (fun a ↦ α.app ⟨K₀, hK₀⟩ ≫ a) hb)
    calc
      _ = standingExceptionalHomEquiv A f hK₀ (plus_rightDerivedUpperShriek_obj g hL)
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map a ≫
            standingExceptionalHomEquiv A g (hK.rightDerivedLowerShriek_obj f) hL
              (α.app ⟨K, hK⟩ ≫ cb)) := hf.symm
      _ = standingExceptionalHomEquiv A f hK₀ (plus_rightDerivedUpperShriek_obj g hL)
          (standingExceptionalHomEquiv A g (hK₀.rightDerivedLowerShriek_obj f) hL
            ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
              ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map a) ≫
                α.app ⟨K, hK⟩ ≫ cb)) :=
        congrArg (standingExceptionalHomEquiv A f hK₀ (plus_rightDerivedUpperShriek_obj g hL))
          hl.symm
      _ = _ := congrArg
        (standingExceptionalHomEquiv A f hK₀ (plus_rightDerivedUpperShriek_obj g hL))
          (congrArg (standingExceptionalHomEquiv A g
            (hK₀.rightDerivedLowerShriek_obj f) hL) hβ)
  exact hsource

private theorem postcompose_image
    {C D : Type*} [Category* C] [Category* D] (ν : C ⥤ D)
    {U V T : D} {Q W R : C}
    (a a' : U ⟶ V) (s : V ⟶ ν.obj W) (f : U ⟶ T) (g : T ⟶ ν.obj Q)
    (c : Q ⟶ W) (b : W ⟶ R)
    (ha : a = a') (h : a' ≫ s = f ≫ g ≫ ν.map c) :
    a ≫ (s ≫ ν.map b) = f ≫ g ≫ ν.map (c ≫ b) := by
  calc
    _ = (a' ≫ s) ≫ ν.map b := by rw [ha, Category.assoc]
    _ = (f ≫ g ≫ ν.map c) ≫ ν.map b := congrArg (fun x ↦ x ≫ ν.map b) h
    _ = _ := by rw [ν.map_comp]; simp only [Category.assoc]

private theorem standingComposition_image
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (α : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⟶
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (hα : α = (originCompositionAmbient A f g).hom)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (counit : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj
      J.obj ⟶ L.obj) :
    let νX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
    let νZ := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
    let hL := (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property).plus
    let hJ := DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj J.property
    let jg := ordinaryStandingComparison A g L.obj L.property
    let LG : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
      ⟨(Etale.rightDerivedUpperShriek A g).obj L.obj,
        Etale.plus_rightDerivedUpperShriek_obj A g L.obj L.property⟩
    let jf := ordinaryStandingComparison A f LG.obj LG.property
    let sh := (fixedCompactSupportComparisonIso A
      (HasCompactification.compactification (f ≫ g))).hom.app J
    let comp := Etale.unboundedEtaleLowerShriekCompIso A f g
    let beta := sh ≫ νZ.map (counit)
    let b : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj J.obj ⟶
        (Etale.rightDerivedUpperShriek A g).obj L.obj :=
      (Etale.rightDerivedUpperShriekAdjunction A g).homEquiv _ _
      (comp.hom.app J.obj ≫ counit)
    standingExceptionalHomEquiv A f hJ (plus_rightDerivedUpperShriek_obj g hL)
        (standingExceptionalHomEquiv A g (hJ.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨νX.obj J.obj, hJ⟩ ≫ beta)) ≫
      (rightDerivedUpperShriek A f).map jg.hom ≫ jf.hom =
      νX.map ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ _ b) := by
  let νX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let νY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let νZ := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
  let hL := (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property).plus
  let hJ := DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj J.property
  let jg := ordinaryStandingComparison A g L.obj L.property
  let LG : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(Etale.rightDerivedUpperShriek A g).obj L.obj,
      Etale.plus_rightDerivedUpperShriek_obj A g L.obj L.property⟩
  let jf := ordinaryStandingComparison A f LG.obj LG.property
  let FG : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj J.obj,
      _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
        ((Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).app J)
        ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj J).property⟩
  let sf := (fixedCompactSupportComparisonIso A
    (HasCompactification.compactification f)).hom.app J
  let sg := (fixedCompactSupportComparisonIso A
    (HasCompactification.compactification g)).hom.app FG
  let sh := (fixedCompactSupportComparisonIso A
    (HasCompactification.compactification (f ≫ g))).hom.app J
  let comp := Etale.unboundedEtaleLowerShriekCompIso A f g
  let beta := sh ≫ νZ.map (counit)
  let b : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj J.obj ⟶
      (Etale.rightDerivedUpperShriek A g).obj L.obj :=
    (Etale.rightDerivedUpperShriekAdjunction A g).homEquiv _ _
    (comp.hom.app J.obj ≫ counit)
  have hword : α.app ⟨νX.obj J.obj, hJ⟩ ≫ beta =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map sf ≫
        sg ≫ νZ.map (comp.hom.app J.obj ≫ counit) := by
    exact postcompose_image νZ
      (U := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj (νX.obj J.obj)))
      (V := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj (νX.obj J.obj))
      (T := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj J.obj)))
      (Q := (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj
        ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj J.obj))
      (W := (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj J.obj)
      (R := L.obj)
      (α.app ⟨νX.obj J.obj, hJ⟩)
      (α.app ⟨νX.obj J.obj, hJ⟩)
      sh ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map sf) sg
      (comp.hom.app J.obj) counit
      rfl
      (originComposition_image A f g α hα J)
  have hg : standingExceptionalHomEquiv A g (hJ.rightDerivedLowerShriek_obj f) hL
      (α.app ⟨νX.obj J.obj, hJ⟩ ≫ beta) ≫ jg.hom = sf ≫ νY.map b := by
    have hw := congrArg
      (standingExceptionalHomEquiv A g (hJ.rightDerivedLowerShriek_obj f) hL) hword
    have hl := standingHom_left A g (hJ.rightDerivedLowerShriek_obj f)
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj FG.property) hL sf
      (sg ≫ νZ.map (comp.hom.app J.obj ≫ counit))
    calc
      _ = standingExceptionalHomEquiv A g (hJ.rightDerivedLowerShriek_obj f) hL
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map sf ≫
            sg ≫ νZ.map (comp.hom.app J.obj ≫ counit)) ≫ jg.hom :=
        congrArg (fun a ↦ a ≫ jg.hom) hw
      _ = (sf ≫ standingExceptionalHomEquiv A g
          (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj FG.property) hL
          (sg ≫ νZ.map (comp.hom.app J.obj ≫ counit))) ≫ jg.hom :=
        congrArg (fun a ↦ a ≫ jg.hom) hl
      _ = sf ≫ νY.map b := by
        simpa only [Category.assoc, sf, sg, νZ, jg, b, FG, νY, hL, Functor.id_obj] using
          congrArg (fun a ↦ sf ≫ a) (standingHom_image A g FG L (comp.hom.app J.obj ≫ counit))
  calc
    _ = standingExceptionalHomEquiv A f hJ
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj LG.property).plus
        (standingExceptionalHomEquiv A g (hJ.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨νX.obj J.obj, hJ⟩ ≫ beta) ≫ jg.hom) ≫ jf.hom := by
      simpa only [Category.assoc] using congrArg (fun a ↦ a ≫ jf.hom)
        (standingHom_right A f hJ (plus_rightDerivedUpperShriek_obj g hL)
          (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj LG.property).plus
          (standingExceptionalHomEquiv A g (hJ.rightDerivedLowerShriek_obj f) hL
            (α.app ⟨νX.obj J.obj, hJ⟩ ≫ beta)) jg.hom).symm
    _ = standingExceptionalHomEquiv A f hJ
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj LG.property).plus
        (sf ≫ νY.map b) ≫ jf.hom :=
      congrArg (fun a ↦ standingExceptionalHomEquiv A f hJ
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj LG.property).plus a ≫
          jf.hom) hg
    _ = νX.map ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ _ b) :=
      standingHom_image A f J LG b


set_option maxHeartbeats 200000 in
-- This Hom-chain calculation compares several large derived-functor expressions.
private theorem standingComposition_ordinary_aux
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (α : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g ⟶
      (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (hα : α = (originCompositionAmbient A f g).hom)
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let hL := (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property).plus
    let K := (rightDerivedUpperShriek A (f ≫ g)).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj L.obj)
    let hK := plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hL
    standingExceptionalHomEquiv A f hK (plus_rightDerivedUpperShriek_obj g hL)
        (standingExceptionalHomEquiv A g (hK.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨K, hK⟩ ≫
            (standingExceptionalHomEquiv A (f ≫ g) hK hL).symm (𝟙 K))) ≫
      (rightDerivedUpperShriek A f).map
        (ordinaryStandingComparison A g L.obj L.property).hom ≫
      (ordinaryStandingComparison A f ((Etale.rightDerivedUpperShriek A g).obj L.obj)
        (Etale.plus_rightDerivedUpperShriek_obj A g L.obj L.property)).hom =
      (ordinaryStandingComparison A (f ≫ g) L.obj L.property).hom ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
          ((conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g))
            ((Etale.rightDerivedUpperShriekAdjunction A f).comp
              (Etale.rightDerivedUpperShriekAdjunction A g))
            (Etale.unboundedEtaleLowerShriekCompIso A f g)).hom.app L.obj) := by
  let νX := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  let νZ := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
  let hL := (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property).plus
  let K := (rightDerivedUpperShriek A (f ≫ g)).obj (νZ.obj L.obj)
  let hK := plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hL
  let J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(Etale.rightDerivedUpperShriek A (f ≫ g)).obj L.obj,
      Etale.plus_rightDerivedUpperShriek_obj A (f ≫ g) L.obj L.property⟩
  let hJ := DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj J.property
  let j := ordinaryStandingComparison A (f ≫ g) L.obj L.property
  let jg := ordinaryStandingComparison A g L.obj L.property
  let LG : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨(Etale.rightDerivedUpperShriek A g).obj L.obj,
      Etale.plus_rightDerivedUpperShriek_obj A g L.obj L.property⟩
  let jf := ordinaryStandingComparison A f LG.obj LG.property
  let sh := (fixedCompactSupportComparisonIso A
    (HasCompactification.compactification (f ≫ g))).hom.app J
  let adjh := Etale.rightDerivedUpperShriekAdjunction A (f ≫ g)
  let comp := Etale.unboundedEtaleLowerShriekCompIso A f g
  let counit : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).obj
      J.obj ⟶ L.obj := adjh.counit.app L.obj
  let cb := (standingExceptionalHomEquiv A (f ≫ g) hK hL).symm (𝟙 K)
  let beta := sh ≫ νZ.map (counit)
  have hb : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map j.inv ≫ cb =
      beta := standingCounit_image A (f ≫ g) L
  have hsource :
      j.inv ≫ standingExceptionalHomEquiv A f hK (plus_rightDerivedUpperShriek_obj g hL)
        (standingExceptionalHomEquiv A g (hK.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨K, hK⟩ ≫ cb)) =
      standingExceptionalHomEquiv A f hJ (plus_rightDerivedUpperShriek_obj g hL)
        (standingExceptionalHomEquiv A g (hJ.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨νX.obj J.obj, hJ⟩ ≫ beta)) :=
    standingTranspose_source A f g hJ hK hL j.inv α cb beta hb
  have hi := standingComposition_image A f g α hα J L counit
  have hm := iterated_transpose_mate (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction A g) adjh comp L.obj
  have hi' := hi.trans (congrArg (fun a ↦ νX.map a) hm)
  change standingExceptionalHomEquiv A f hK (plus_rightDerivedUpperShriek_obj g hL)
      (standingExceptionalHomEquiv A g (hK.rightDerivedLowerShriek_obj f) hL
        (α.app ⟨K, hK⟩ ≫ cb)) ≫ (rightDerivedUpperShriek A f).map jg.hom ≫ jf.hom =
    j.hom ≫ νX.map ((conjugateIsoEquiv adjh
      ((Etale.rightDerivedUpperShriekAdjunction A f).comp
        (Etale.rightDerivedUpperShriekAdjunction A g)) comp).hom.app L.obj)
  apply cancel_inv_source j
  simp only [← Category.assoc]
  calc
    _ = standingExceptionalHomEquiv A f hJ (plus_rightDerivedUpperShriek_obj g hL)
        (standingExceptionalHomEquiv A g (hJ.rightDerivedLowerShriek_obj f) hL
          (α.app ⟨νX.obj J.obj, hJ⟩ ≫ beta)) ≫
        (rightDerivedUpperShriek A f).map jg.hom ≫ jf.hom := by
      simpa only [Category.assoc] using congrArg
        (fun a ↦ a ≫ (rightDerivedUpperShriek A f).map jg.hom ≫ jf.hom) hsource
    _ = _ := hi'

private theorem standingComposition_ordinary
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let hL := (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj L.property).plus
    let K := (rightDerivedUpperShriek A (f ≫ g)).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.obj L.obj)
    let hK := plusEtaleOrigin_rightDerivedUpperShriek_obj (f ≫ g) hL
    ((standingExceptionalHomEquiv A g (hK.rightDerivedLowerShriek_obj f) hL).trans
      (standingExceptionalHomEquiv A f hK (plus_rightDerivedUpperShriek_obj g hL)))
        ((originCompositionAmbient A f g).hom.app ⟨K, hK⟩ ≫
          (standingExceptionalHomEquiv A (f ≫ g) hK hL).symm (𝟙 K)) ≫
      (rightDerivedUpperShriek A f).map
        (ordinaryStandingComparison A g L.obj L.property).hom ≫
      (ordinaryStandingComparison A f ((Etale.rightDerivedUpperShriek A g).obj L.obj)
        (Etale.plus_rightDerivedUpperShriek_obj A g L.obj L.property)).hom =
      (ordinaryStandingComparison A (f ≫ g) L.obj L.property).hom ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
          ((conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction A (f ≫ g))
            ((Etale.rightDerivedUpperShriekAdjunction A f).comp
              (Etale.rightDerivedUpperShriekAdjunction A g))
            (Etale.unboundedEtaleLowerShriekCompIso A f g)).hom.app L.obj) := by
  exact standingComposition_ordinary_aux A f g (originCompositionAmbient A f g).hom rfl L

end AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

private theorem diagonal_standing_comparison (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (P.chartDiagonalDualizingStanding f).inv ≫ (P.diagonalDualizingComparison f).hom =
      (ProEtale.ordinaryStandingComparison P.Coefficient f
        (Etale.ordinaryFiniteUnit P.Coefficient Y) (P.diagonalUnitPlus Y)).hom := by
  simp only [chartDiagonalDualizingStanding, diagonalDualizingComparison,
    ProEtale.ordinaryStandingComparison, Functor.mapIso_inv, Functor.mapIso_hom,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    ← Functor.map_comp]
  congr 1
  simp [Etale.rightDerivedUpperShriekAdjunction]

private theorem chartEtaleIdentification_hom
    (P : PurityFiniteSetting.{u}) {U X : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [HasCompactification e]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (K : Etale.DerivedCategoryModule P.Coefficient X)
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    (P.chartEtaleIdentification e N K hK).hom =
      (ProEtale.ordinaryStandingComparison P.Coefficient e K hK).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.map
            (((N.adjunction e (HasCompactification.compactification e)
              (Etale.rightDerivedUpperShriek P.Coefficient e)
              (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e)).exists.choose).hom.app K) ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.map
            ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} P.Coefficient) e).inv.app K) ≫
        (Dnc.pullComparison P e K).inv := by
  simp only [chartEtaleIdentification, ProEtale.ordinaryStandingComparison,
    Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]

end WeilConjectures.PurityFiniteSetting.ChartComparisons

namespace AlgebraicGeometry.Etale

private theorem normalization_comparison_canonical
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e) :
    N.comparison e c = canonicalEtaleCompactSupportComparison A e c := by
  exact EtaleSupportExchange.normalized_comparison_eq A e c
    (N.sheafComparison e c) (N.comparison e c)
    (N.sheaf_normalization e c) (N.derived_normalization e c)

private theorem ambientLeft_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (e : U ⟶ X) (g : X ⟶ Y)
    [Etale e] [IsSeparated e] [QuasiCompact e]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification e] [HasCompactification g] [HasCompactification (e ≫ g)] :
    (etaleAmbientLeftComparison A N e g
      (HasCompactification.compactification g)
      (HasCompactification.compactification (e ≫ g))).hom =
      Functor.whiskerRight (N.comparison e
        (HasCompactification.compactification e)).inv
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g) ≫
      (unboundedEtaleLowerShriekCompIso A e g).hom := by
  let c := HasCompactification.compactification e
  let d := HasCompactification.compactification g
  let k := HasCompactification.compactification (e ≫ g)
  let r := (k.ofComp d).restrict
  have hn := EtaleSupportExchange.comparison_refinement A e r c
  erw [← normalization_comparison_canonical A N e r,
    ← normalization_comparison_canonical A N e c] at hn
  have hi : (N.comparison e r).inv =
      (N.comparison e c).inv ≫ (rightDerivedLowerShriekIso A r).inv := by
    have hi : rightDerivedLowerShriekIso A r ≪≫ N.comparison e c =
        N.comparison e r := Iso.ext hn
    exact (congrArg Iso.inv hi).symm
  simp only [etaleAmbientLeftComparison, unboundedEtaleLowerShriekCompIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
  erw [hi, Functor.whiskerRight_comp]
  simp only [Category.assoc]
  rfl

set_option maxHeartbeats 200000 in
-- Instantiate the mate-composition laws on unbounded derived functors.
private theorem ordinary_etale_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    (e : U ⟶ X) (g : X ⟶ Y)
    [Etale e] [IsSeparated e] [QuasiCompact e]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification e] [HasCompactification g] [HasCompactification (e ≫ g)]
    (B : DerivedCategoryModule A Y) :
    (conjugateIsoEquiv (rightDerivedUpperShriekAdjunction A (e ≫ g))
        ((rightDerivedUpperShriekAdjunction A e).comp
          (rightDerivedUpperShriekAdjunction A g))
        (unboundedEtaleLowerShriekCompIso A e g)).hom.app B ≫
      ((N.adjunction e (HasCompactification.compactification e)
        (rightDerivedUpperShriek A e)
        (rightDerivedUpperShriekAdjunction A e)).exists.choose).hom.app
          ((rightDerivedUpperShriek A g).obj B) =
      (tensorMateEtalePrecompLocalityIso A N e g).inv.app B := by
  let adj := rightDerivedUpperShriekAdjunction A e
  let sumAdj := (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
    inferInstance).mapDerivedCategoryAdjunction
  let n := N.comparison e (HasCompactification.compactification e)
  let q := conjugateIsoEquiv adj sumAdj n.symm
  have hq : Functor.whiskerLeft (rightDerivedUpperShriek A e) n.hom ≫
      Functor.whiskerRight q.hom
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ≫
      sumAdj.counit = adj.counit := by
    ext K
    change n.hom.app _ ≫
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
        ((conjugateEquiv adj sumAdj n.inv).app K) ≫ sumAdj.counit.app K =
      adj.counit.app K
    erw [conjugateEquiv_counit adj sumAdj n.inv]
    simp
  have hchoice : (N.adjunction e (HasCompactification.compactification e)
      (rightDerivedUpperShriek A e) adj).exists.choose = q :=
    (N.adjunction e (HasCompactification.compactification e)
      (rightDerivedUpperShriek A e) adj).unique
        (N.adjunction e (HasCompactification.compactification e)
          (rightDerivedUpperShriek A e) adj).exists.choose_spec hq
  erw [hchoice]
  change (conjugateEquiv _ (adj.comp _) _).app B ≫
      (conjugateEquiv adj sumAdj n.inv).app _ =
    (conjugateEquiv _ (sumAdj.comp _) _).app B
  have h := congr_app (conjugateEquiv_comp
    (rightDerivedUpperShriekAdjunction A (e ≫ g))
    (adj.comp (rightDerivedUpperShriekAdjunction A g))
    (sumAdj.comp (rightDerivedUpperShriekAdjunction A g))
    (unboundedEtaleLowerShriekCompIso A e g).hom
    (Functor.whiskerRight n.inv (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g))) B
  erw [conjugateEquiv_whiskerRight adj sumAdj
    (rightDerivedUpperShriekAdjunction A g) n.inv] at h
  erw [ambientLeft_composition]
  exact h

end AlgebraicGeometry.Etale

namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

private theorem chart_diagram
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (H : C ⥤ E) (ν : D ⥤ E)
    {a b c : C} {h k l n : D} {x y w v : E}
    (S : a ≅ b) (D₀ : a ≅ c) (γg : b ≅ c)
    (T : x ≅ y) (E₀ : x ≅ ν.obj h) (γh : y ≅ ν.obj h)
    (γe : H.obj c ≅ ν.obj k) (I : H.obj c ≅ w) (J : n ≅ h)
    (s : y ⟶ H.obj b) (p : ν.obj n ⟶ w) (z : w ⟶ v)
    (m : h ⟶ k) (q : k ⟶ l) (r : l ⟶ n) (t : h ⟶ l)
    (hs : S.inv ≫ D₀.hom = γg.hom) (ht : T.inv ≫ E₀.hom = γh.hom)
    (hc : s ≫ H.map γg.hom ≫ γe.hom = γh.hom ≫ ν.map m)
    (hi : I.hom = γe.hom ≫ ν.map q ≫ ν.map r ≫ p)
    (hm : m ≫ q = t) (hj : J.inv = t ≫ r) :
    s ≫ H.map S.inv ≫ H.map D₀.hom ≫ I.hom ≫ z =
      T.inv ≫ E₀.hom ≫ ν.map J.inv ≫ p ≫ z := by
  calc
    _ = s ≫ H.map (S.inv ≫ D₀.hom) ≫ I.hom ≫ z := by
      rw [H.map_comp]
      simp only [Category.assoc]
    _ = s ≫ H.map γg.hom ≫ γe.hom ≫ ν.map q ≫ ν.map r ≫ p ≫ z := by
      rw [hs, hi]
      simp only [Category.assoc]
    _ = γh.hom ≫ ν.map m ≫ ν.map q ≫ ν.map r ≫ p ≫ z := by
      simpa only [Category.assoc] using
        congrArg (fun a ↦ a ≫ ν.map q ≫ ν.map r ≫ p ≫ z) hc
    _ = γh.hom ≫ ν.map t ≫ ν.map r ≫ p ≫ z := by
      rw [← ν.map_comp_assoc, hm]
    _ = T.inv ≫ E₀.hom ≫ ν.map J.inv ≫ p ≫ z := by
      rw [hj, ν.map_comp, ← ht]
      simp only [Category.assoc]

attribute [local irreducible] ProEtale.ordinaryStandingComparison composition
  chartDiagonalDualizingStanding diagonalDualizingComparison Dnc.pullComparison

set_option maxHeartbeats 200000 in
-- The specialization unfolds the chart and derived-functor comparison data.
/-- Specialize the ordinary Hom-chain calculation to the coefficient unit and unfold
only the chart and standing composition wrappers. Explicit congruences retain the cached
comparison instances throughout the calculation.
Source: orientation-charts Step 3 (blueprint: lem-pur-chart-exceptional-counit-equation). -/
private theorem chart_composition_calculation (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B) :
  letI := Dnc.compactifiable P B.proj aV
  letI := Dnc.compactifiable P e.hom (B.proj ≫ aV)
  letI := Dnc.compactifiable P (e.hom ≫ B.proj) aV
  letI := P.noetherian aV
  letI := P.noetherian (B.proj ≫ aV)
  letI := P.noetherian ((e.hom ≫ B.proj) ≫ aV)
  let H := ProEtale.rightDerivedUpperShriek P.Coefficient e.hom
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) C.X).mapDerivedCategory
  let L : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
    ⟨Etale.ordinaryFiniteUnit P.Coefficient V, P.diagonalUnitPlus V⟩
  composition P B.proj aV e.hom ≫
      H.map (ProEtale.ordinaryStandingComparison P.Coefficient B.proj
        L.obj L.property).hom ≫
      (ProEtale.ordinaryStandingComparison P.Coefficient e.hom
        (P.diagonalOrdinaryDualizing B.proj)
        (Etale.plus_rightDerivedUpperShriek_obj P.Coefficient B.proj L.obj L.property)).hom =
      (ProEtale.ordinaryStandingComparison P.Coefficient (e.hom ≫ B.proj)
        L.obj L.property).hom ≫ ν.map
          ((conjugateIsoEquiv
            (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (e.hom ≫ B.proj))
            ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient e.hom).comp
              (Etale.rightDerivedUpperShriekAdjunction P.Coefficient B.proj))
            (Etale.unboundedEtaleLowerShriekCompIso
              P.Coefficient e.hom B.proj)).hom.app L.obj) := by
  let := Dnc.compactifiable P B.proj aV
  let := Dnc.compactifiable P e.hom (B.proj ≫ aV)
  let := Dnc.compactifiable P (e.hom ≫ B.proj) aV
  let := P.noetherian aV
  let := P.noetherian (B.proj ≫ aV)
  let := P.noetherian ((e.hom ≫ B.proj) ≫ aV)
  run_tac Lean.Elab.Tactic.withMainContext do
    let coeff := Lean.mkIdent `P.Coefficient
    let f := Lean.mkIdent `e.hom
    let g := Lean.mkIdent `B.proj
    let unitPlus := Lean.mkIdent `P.diagonalUnitPlus
    let base := Lean.mkIdent `V
    let input ← Lean.Elab.Term.elabTerm (← `(ProEtale.standingComposition_ordinary
      $coeff $f $g (⟨Etale.ordinaryFiniteUnit $coeff $base, $unitPlus $base⟩))) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let input ← Lean.instantiateMVars input
    let actual ← Lean.instantiateMVars (← Lean.Meta.inferType input)
    let expected ← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let h ← chartInstanceHEq cache actual expected 3000
    let h := Lean.mkAppN (Lean.mkConst ``eq_of_heq [.succ .zero])
      #[Lean.mkSort .zero, actual, expected, h]
    let input ← Lean.Meta.mkAuxTheorem actual input
      (zetaDelta := true) (kind? := `_chart_input)
    let h ← Lean.Meta.mkAuxTheorem (← Lean.Meta.mkEq actual expected) h
      (zetaDelta := true) (kind? := `_chart_prop_eq)
    let proof := Lean.mkAppN (Lean.mkConst ``Eq.mp [.zero])
      #[actual, expected, h, input]
    let proof ← Lean.Meta.mkAuxTheorem expected proof
      (zetaDelta := true) (kind? := `_chart_final_cast)
    (← Lean.Elab.Tactic.getMainGoal).assign proof

/-- Standing exceptional composition followed by the normalized etale identification
is the canonical dualizing locality comparison, in standing exceptional coordinates.
Source: orientation-charts proof Step 3, composing adjunctions and etale locality
(blueprint: lem-pur-chart-exceptional-counit-equation).

Proof: Identify the standing Hom bijections with the normalized comparison-class
adjunction on bounded-below etale-origin objects. Normalization on ordinary etale
representatives and naturality through the chosen antecedent isomorphisms give
naturality in both variables and the ordinary transpose formula. The restriction
of the canonical origin compositor, together with bounded-below compositor
compatibility, computes the successive standing transposes as the ordinary
adjunction conjugate, retaining the comparison-unit isomorphisms.

Graph normalization identifies the compact-support presentation with the canonical
etale comparison. Its compactification-change compatibility and uniqueness of the
counit-normalized right-adjoint comparison identify ordinary exceptional composition
followed by chartEtaleIdentification with inverse etale locality. Finally,
chartDiagonalDualizingStanding.inv followed by diagonalDualizingComparison is the
comparison-unit isomorphism. Cancel these factors, apply the two composition
calculations, and expand diagonalEtaleLocality to obtain exactly rho and epsilon. -/
theorem chart_exceptional_counit_equation (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := Dnc.compactifiable P B.proj aV
    letI := Dnc.compactifiable P e.hom (B.proj ≫ aV)
    letI := Dnc.compactifiable P (e.hom ≫ B.proj) aV
    composition P B.proj aV e.hom ≫
        (ProEtale.rightDerivedUpperShriek P.Coefficient e.hom).map
          (P.chartDiagonalDualizingStanding B.proj).inv ≫ (rho P B.proj aV e.hom N).hom =
      (P.chartDiagonalDualizingStanding (e.hom ≫ B.proj)).inv ≫
        (epsilon P B.proj aV e.hom N).hom := by
  let := Dnc.compactifiable P B.proj aV
  let := Dnc.compactifiable P e.hom (B.proj ≫ aV)
  let := Dnc.compactifiable P (e.hom ≫ B.proj) aV
  let := P.noetherian aV
  let := P.noetherian (B.proj ≫ aV)
  let := P.noetherian ((e.hom ≫ B.proj) ≫ aV)
  let H := ProEtale.rightDerivedUpperShriek P.Coefficient e.hom
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) C.X).mapDerivedCategory
  let L : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
    ⟨Etale.ordinaryFiniteUnit P.Coefficient V, P.diagonalUnitPlus V⟩
  have hc := chart_composition_calculation P aV e
  have ho := Etale.ordinary_etale_composition P.Coefficient N e.hom B.proj L.obj
  have hs := diagonal_standing_comparison P B.proj
  have ht := diagonal_standing_comparison P (e.hom ≫ B.proj)
  let S := P.chartDiagonalDualizingStanding B.proj
  let T := P.chartDiagonalDualizingStanding (e.hom ≫ B.proj)
  let D := P.diagonalDualizingComparison B.proj
  let E := P.diagonalDualizingComparison (e.hom ≫ B.proj)
  let γg := ProEtale.ordinaryStandingComparison P.Coefficient B.proj L.obj L.property
  let γe := ProEtale.ordinaryStandingComparison P.Coefficient e.hom
    (P.diagonalOrdinaryDualizing B.proj)
    (Etale.plus_rightDerivedUpperShriek_obj P.Coefficient B.proj L.obj L.property)
  let γh := ProEtale.ordinaryStandingComparison P.Coefficient (e.hom ≫ B.proj)
    L.obj L.property
  let I := P.chartEtaleIdentification e.hom N (P.diagonalOrdinaryDualizing B.proj)
    (Etale.plus_rightDerivedUpperShriek_obj P.Coefficient B.proj L.obj L.property)
  let J := P.diagonalEtaleLocality N e.hom B.proj
  let p := (Dnc.pullComparison P e.hom (P.diagonalOrdinaryDualizing B.proj)).inv
  let z := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.map
    D.inv
  let q := ((N.adjunction e.hom (HasCompactification.compactification e.hom)
    (Etale.rightDerivedUpperShriek P.Coefficient e.hom)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient e.hom)).exists.choose).hom.app
      (P.diagonalOrdinaryDualizing B.proj)
  let r := (Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) e.hom).inv.app (P.diagonalOrdinaryDualizing B.proj)
  let m := (conjugateIsoEquiv
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (e.hom ≫ B.proj))
    ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient e.hom).comp
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient B.proj))
    (Etale.unboundedEtaleLowerShriekCompIso P.Coefficient e.hom B.proj)).hom.app L.obj
  let t := (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N e.hom B.proj).inv.app
    L.obj
  have hi : I.hom = γe.hom ≫ ν.map q ≫ ν.map r ≫ p :=
    chartEtaleIdentification_hom P e.hom N (P.diagonalOrdinaryDualizing B.proj)
      (Etale.plus_rightDerivedUpperShriek_obj P.Coefficient B.proj L.obj L.property)
  have hm : m ≫ q = t := ho
  have hj : J.inv = t ≫ r := by
    simp only [J, diagonalEtaleLocality, Iso.trans_inv, Iso.app_inv,
      t, r, L, diagonalOrdinaryDualizing]
  simp only [rho, epsilon, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  exact chart_diagram H ν S D γg T E γh γe I J
    (composition P B.proj aV e.hom) p z m q r t hs ht hc hi hm hj

end WeilConjectures.PurityFiniteSetting.ChartComparisons
