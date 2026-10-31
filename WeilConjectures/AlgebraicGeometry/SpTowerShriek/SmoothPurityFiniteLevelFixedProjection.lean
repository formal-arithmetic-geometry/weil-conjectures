/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicRealizationOriginComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-! # Finite-level projection: fixed origins -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- Keep coefficient instances on the path used by the generic finite-ring theorem.
attribute [local instance 2000] CommRing.toRing

private def LevelGood (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory T A) : Prop :=
  Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj K)} ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
    HasFiniteProEtaleTorAmplitude T A K

private theorem quotient_good (T : Scheme.{u})
    (I J : Ideal (Padic.coefficientExtensionIntegers l E)) (h : I = J)
    [Finite (Padic.coefficientExtensionIntegers l E ⧸ I)]
    [Finite (Padic.coefficientExtensionIntegers l E ⧸ J)]
    (K : proEtaleDerivedCategory T (Padic.coefficientExtensionIntegers l E ⧸ I))
    (hK : LevelGood T (Padic.coefficientExtensionIntegers l E ⧸ J)
      ((quotientTransport l E T I J h).obj K)) :
    LevelGood T (Padic.coefficientExtensionIntegers l E ⧸ I) K := by
  subst J
  exact hK

private theorem levelGood_iso {T : Scheme.{u}} {A : Type u} [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (h : LevelGood T A K) :
    LevelGood T A L := by
  refine ⟨h.1.subset (fun i hi hz ↦ hi
    (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)), ?_, ?_⟩
  · intro i
    have hi := h.2.1 i
    rw [proEtaleModuleRestriction_constructible_iff] at hi ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction T A).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) hi
  · obtain ⟨a, b, ht⟩ := h.2.2
    refine ⟨a, b, ht.1, ?_⟩
    intro N P hN f hf hP M i hi
    exact ht.2 N P (hN.map (fun q ↦ q ≪≫ e.symm)) f hf hP M i hi

private theorem bounded_of_finite_support
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C)
    (h : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor C i).obj K)}) :
    DerivedCategory.TStructure.t.bounded K := by
  obtain ⟨a, ha⟩ := h.bddBelow
  obtain ⟨b, hb⟩ := h.bddAbove
  refine ⟨⟨a, (DerivedCategory.isGE_iff K a).mpr (fun i hi ↦ ?_)⟩,
    ⟨b, (DerivedCategory.isLE_iff K b).mpr (fun i hi ↦ ?_)⟩⟩
  · by_contra hz
    exact (not_lt_of_ge (ha hz)) hi
  · by_contra hz
    exact (not_lt_of_ge (hb hz)) hi

private theorem levelGood_fixed (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : DerivedCategory (Sheaf (ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (h : LevelGood T A ((sfIntrinsicModuleEquivalence T A).functor.mapDerivedCategory.obj K)) :
    ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T K := by
  let F := (sfIntrinsicModuleEquivalence T A).functor
  have hb := F.bounded_of_bounded_mapDerivedCategory_obj
    (bounded_of_finite_support _ h.1)
  have hc (i : ℤ) : ProEtale.IsConstructible (ULift.{u + 1, u} A)
      ((DerivedCategory.homologyFunctor _ i).obj K) := by
    let e := (F.mapDerivedCategoryHomologyFunctorIso i).app K
    have hh := h.2.1 i
    rw [proEtaleModuleRestriction_constructible_iff] at hh
    have hr := (proEtaleModuleRestriction T A).mapIso e.symm
    have hreal := ProEtale.isConstructible_of_iso hr hh
    obtain ⟨er⟩ := ProEtale.intrinsicRealization_restriction T A
    exact ProEtale.isConstructible_of_iso
      (er.app ((DerivedCategory.homologyFunctor _ i).obj K)) hreal
  have hbc := ProEtale.DerivedCategory.boundedConstructible_of_homology
    (ULift.{u + 1, u} A) hb (fun i ↦
      ProEtale.exists_isConstructibleSheaf_iso_comparisonUpperStar_obj _ (hc i))
  obtain ⟨a, b, ht⟩ := h.2.2
  exact ⟨hbc, a, b, (intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    A T a b ht.1 K).mp ht⟩

private theorem goodLevel_fixed (b : Base l E) (T : Scheme.{u}) (n : ℕ)
    (K : D l E T) (w : Origin l E b T n K) (h : GoodLevel l E b T n K) :
    ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n))) T w.level.obj := by
  have : Finite (Padic.coefficientExtensionRing l E (b.ramification * (n + 1))) :=
    Padic.finite_coefficientExtensionRing l E _
      (Nat.mul_pos b.ramification_positive (Nat.succ_pos n))
  have hg : LevelGood T (R l E n) ((Ev l E T n).obj K) := by
    exact quotient_good l E T (spEllIdeal l E ^ (n + 1))
      (Padic.coefficientExtensionIdeal l E (b.ramification * (n + 1)))
      (b.ideals n) ((Ev l E T n).obj K) ⟨h.1.1, h.1.2, h.2⟩
  exact levelGood_fixed T (R l E n) w.level.obj (levelGood_iso w.realization.symm hg)

private theorem lifted_projection_map_isIso (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (L : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hK : ProEtale.DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X K)
    (hL : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y L)
    {C : Type*} [Category C]
    (F : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ⥤ C) :
    IsIso (F.map (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app K).app L)) := by
  have hp : IsIso (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).app K).app L) :=
    hasProjectionFormulaOfCompactification_of_boundedConstructible
      (ULift.{u + 1, u} A) c hK hL
  exact F.map_isIso _

attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor projectionMapOfCompactification

attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  SheafOfModules.OpenTensorNormalization.finiteTensor

private meta def projectionHeadAsApplication (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let f := e.getAppFn.consumeMData
  if let .proj n i v := f then
    let env ← Lean.getEnv
    let some info := Lean.getStructureInfo? env n | throwError "unknown structure {n}"
    let some p := Lean.getProjFnForField? env n (info.fieldNames[i]!) |
      throwError "unknown projection {n} {i}"
    let t ← Lean.Meta.whnfD (← Lean.Meta.inferType v)
    let .const _ us := t.getAppFn | throwError "projection has non-structure argument"
    let f := Lean.mkAppN (.const p us) (t.getAppArgs.push v)
    return Lean.mkAppN f e.getAppArgs
  return e

/- Factor coefficient-instance equalities at argument boundaries and cache them.
This is the proof-generating congruence used by FiniteIntrinsicProjectionCoordinates;
every generated equality is checked by Lean's kernel. -/
private meta def coefficientInstanceCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "congruence recursion limit"
  | fuel + 1 =>
    let (_, g) ← g.intros
    g.withContext do
      let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let entries ← cache.get
      if let some pf := entries[t]? then
        g.assign pf
        return
      for d in ← Lean.getLCtx do
        if (← Lean.instantiateMVars d.type).consumeMData == t then
          g.assign d.toExpr
          return
      let (a, b) ← if let some (_, a, b) := t.eq? then pure (a, b)
        else if let some (_, a, _, b) := t.heq? then pure (a, b)
        else throwError "unexpected congruence goal {t}"
      let a := a.consumeMData
      let b := b.consumeMData
      for d in ← Lean.getLCtx do
        let dt := (← Lean.instantiateMVars d.type).consumeMData
        if let some (_, x, _, y) := dt.heq? then
          if t.isHEq && x.consumeMData == a && y.consumeMData == b then
            g.assign d.toExpr
            return
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else
        let a ← projectionHeadAsApplication a
        let b ← projectionHeadAsApplication b
        let common := a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0
        let a ← if common then pure a else
          projectionHeadAsApplication (← Lean.Meta.whnfD a)
        let b ← if common then pure b else
          projectionHeadAsApplication (← Lean.Meta.whnfD b)
        if a == b then
          if t.isHEq then g.hrefl else g.refl
        else if ← g.proofIrrelHeq then pure ()
        else if t.isEq then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
            { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else if a.isLambda && b.isLambda then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``Function.hfunext)
            { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else if a.getAppFn == b.getAppFn &&
            a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
          let f := a.getAppFn
          let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
          let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
          let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
            (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
          let mut pf := c.proof.beta #[f]
          for i in [:a.getAppNumArgs] do
            let k := c.argKinds[i + 1]!
            pf := Lean.mkApp pf a.getAppArgs[i]!
            unless k == .fixed do
              pf := Lean.mkApp pf b.getAppArgs[i]!
              if k == .eq || k == .heq then
                let ty ← Lean.Meta.whnfD (← Lean.Meta.inferType pf)
                unless ty.isForall do throwError "missing congruence equality binder"
                let h ← Lean.Meta.mkFreshExprMVar ty.bindingDomain!
                pf := Lean.mkApp pf h
                coefficientInstanceCongr cache fuel h.mvarId!
              else unless k == .subsingletonInst do
                throwError "unsupported congruence argument kind"
          g.assign pf
        else
          throwError "unsupported congruence at fuel {fuel}:\n{a}\nversus\n{b}"
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)


set_option maxHeartbeats 2000000 in
-- Checking the concrete quotient-ring projection endpoints needs additional kernel reductions.
/-- The finite projection on the retained fixed-scalar origins is invertible after
canonical realization. No tensor or compactification comparison data is involved.
Source: blueprint operations proof (2a); finite compact-support projection formula;
comparison Tor amplitude (ii)
(blueprint: lem-sp-finite-level-projection-fixed-realization).

Proof: identify the ell-power quotient with the positive uniformizer-power quotient
using `b.ideals n`. Transport GoodLevel through this identity-on-integers quotient
identification. Exact intrinsic realization preserves cohomology and identifies
constructibility and finite Tor intervals with their fixed-scalar counterparts.
Use each retained realization isomorphism to obtain these properties for the
specified fixed-scalar origin. Fully faithful site comparison reflects the
bounded cohomology support and constructibility to its etale antecedent. Comparison
Tor amplitude (ii) reflects the interval for the second antecedent. The coefficient
prime is invertible on the schemes since `hlp` excludes the residue characteristic.
Apply the finite compact-support projection theorem to these antecedents and the
supplied compactification. Naturality conjugates its projection map along the
retained fixed-scalar origin isomorphisms. All conjugating factors are isomorphisms;
canonical realization preserves the resulting isomorphism. Empty schemes, zero
objects, and a one-degree Tor interval require no separate choices. -/
theorem finite_level_fixed_realization_isIso (b : Base l E)
    (k : FiniteFieldDatum.{u}) (hlp : l ≠ k.p)
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (c : Compactification f.left) (n : ℕ)
    (K : D l E X.left) (L : D l E Y.left)
    (wK : Origin l E b X.left n K) (wL : Origin l E b Y.left n L)
    (hK : GoodLevel l E b X.left n K) (hL : GoodLevel l E b Y.left n L) :
    IsIso ((comparisonFiniteRealization l E b Y.left n).map
      (comparisonFiniteProjection l E b c n wK.level.obj wL.level.obj)) := by
  have _hchar := hlp
  have hKfixed := goodLevel_fixed l E b X.left n K wK hK
  have hLfixed := goodLevel_fixed l E b Y.left n L wL hL
  have hm := lifted_projection_map_isIso (R l E n) c
    wK.level.obj wL.level.obj hKfixed.1 hLfixed
    (comparisonFiniteRealization l E b Y.left n)
  simp only [comparisonFiniteProjection,
    SheafOfModules.OpenTensorNormalization.finiteTensor, id,
    Functor.uncurry_obj_obj, derivedTensorRightDerivedLowerShriek_obj_obj,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj] at hm ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let some r := (← Lean.getLCtx).findFromUserName? `hm |
      throwError "missing mapped projection isomorphism"
    let g ← Lean.Elab.Tactic.getMainGoal
    let src ← Lean.instantiateMVars (← Lean.Meta.inferType r.toExpr)
    let tgt ← Lean.instantiateMVars (← g.getType)
    let v ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq src tgt)
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[v, r.toExpr])
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    Lean.Meta.withTransparency .default do
      coefficientInstanceCongr cache 100 v.mvarId!
    Lean.Elab.Tactic.replaceMainGoal []

end AlgebraicGeometry.ProEtale.SpTowerShriek
