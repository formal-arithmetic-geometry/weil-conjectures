/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionEvaluationFactors
public import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionFormulaCoherence
public import WeilConjectures.SixFunctors.IntegralProjectionReduction.CanonicalFiniteIntrinsicTensorComparison
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionProperFactor
import WeilConjectures.SixFunctors.IntegralProjectionReduction.FiniteIntrinsicProjectionOpenFactor
import Mathlib.Lean.Meta.CongrTheorems

/-! # Compatibility of a finite intrinsic projection realization

Source: fix-prop-projection-formula.proof.md, comparison of the same projection map.
(blueprint: new-sf-finite-intrinsic-projection-compatibility).

Proof: transpose the proper and open factors through their actual adjunctions,
using the normalized inverse-image comparison. Naturality of the tensor, support,
and finite pullback comparisons then transports the two ambient finite inputs. The
resulting pasted square is exactly the fixed-presentation component. This statement
uses the explicitly constructed tensor comparison and pastes its proper and open
factor equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus sfIntrinsicDerivedEquivalence

/- Native factor statements preserve all data fields. At the final boundary we
normalize beta redexes, identity functors, the support composite and the inclusion
object projection, then use congruence and proof irrelevance. -/
private meta def coefficientInstanceCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "congruence recursion limit"
  | fuel + 1 =>
    let (_, g) ← g.intros
    g.withContext do
      let t ← Lean.instantiateMVars (← g.getType)
      let entries ← cache.get
      if let some pf := entries[t]? then
        g.assign pf
        return
      let (a, b) ← if let some (_, a, b) := t.eq? then pure (a, b)
        else if let some (_, a, _, b) := t.heq? then pure (a, b)
        else throwError "unexpected congruence goal {t}"
      let a := a.consumeMData.headBeta
      let b := b.consumeMData.headBeta
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else
        let a ← match a with
          | .letE .. => Lean.Meta.whnf a
          | _ =>
            if a.getAppFn.isConstOf ``CategoryTheory.Functor.obj then
              let F := a.getAppArgs[4]!
              if F.getAppFn.isConstOf ``CategoryTheory.Functor.id then
                pure a.getAppArgs.back!
              else if F.getAppFn.isConstOf ``sixFunctorFiniteSupport ||
                  F.getAppFn.isConstOf ``sfAmbientCompactSupportCandidate then
                Lean.Meta.whnf a
              else if F.getAppFn.isConstOf ``CategoryTheory.Functor.comp &&
                  F.getAppArgs.back!.getAppFn.isConstOf ``CategoryTheory.ObjectProperty.ι then
                Lean.Meta.whnf a else pure a
            else pure a
        let b ← match b with
          | .letE .. => Lean.Meta.whnf b
          | _ =>
            if b.getAppFn.isConstOf ``CategoryTheory.Functor.obj then
              let F := b.getAppArgs[4]!
              if F.getAppFn.isConstOf ``CategoryTheory.Functor.id then
                pure b.getAppArgs.back!
              else if F.getAppFn.isConstOf ``sixFunctorFiniteSupport ||
                  F.getAppFn.isConstOf ``sfAmbientCompactSupportCandidate then
                Lean.Meta.whnf b
              else if F.getAppFn.isConstOf ``CategoryTheory.Functor.comp &&
                  F.getAppArgs.back!.getAppFn.isConstOf ``CategoryTheory.ObjectProperty.ι then
                Lean.Meta.whnf b else pure b
            else pure b
        if a == b then
          if t.isHEq then g.hrefl else g.refl
        else if ← g.proofIrrelHeq then pure ()
        else if t.isEq then
          let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
            { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else if a.getAppFn == b.getAppFn &&
            a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
          let f := a.getAppFn
          let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
          let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
          let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
            (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
          let gs ← g.apply (c.proof.beta #[f]) { synthAssignedInstances := false }
          for g in gs do coefficientInstanceCongr cache fuel g
        else
          if t.isHEq then g.hrefl else g.refl
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)

private theorem paste_factors
    {A : Type*} [Category A] {P M R U V W N Q : A}
    {p : P ⟶ M} {d : M ⟶ R} {t : R ⟶ Q} {s : P ⟶ U}
    {a : U ⟶ V} {b : V ⟶ W} {mid : M ⟶ W}
    {tail : W ⟶ N} {out : N ⟶ Q}
    (hp : p ≫ mid = s ≫ a ≫ b)
    (ho : mid ≫ tail ≫ out = d ≫ t) :
    p ≫ d ≫ t = s ≫ (a ≫ b ≫ tail ≫ out) := by
  rw [← ho, ← Category.assoc p mid, hp]
  simp only [Category.assoc]

private theorem reassociate_words
    {A : Type*} [Category A] {P Q R T N Z S W : A}
    {p : P ⟶ Q} {q : Q ⟶ R} {r : R ⟶ T} {t : T ⟶ N} {out : N ⟶ Z}
    {s₁ : P ⟶ S} {s₂ : S ⟶ W} {z : W ⟶ Z}
    (h : p ≫ (q ≫ r) ≫ (t ≫ out) = (s₁ ≫ s₂) ≫ z) :
    (p ≫ q ≫ r) ≫ t ≫ out = s₁ ≫ s₂ ≫ z := by
  simpa only [Category.assoc] using h

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor AlgebraicGeometry.ProEtale.derivedTensor
  finiteIntrinsicDerivedTensor sfIntrinsicModuleEquivalence
  SystemProjectionFormula.finiteProperProjection
  SystemProjectionFormula.finiteOpenTensorInv SystemProjectionFormula.finitePullComp

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory in
/-- Projection compatibility for the specified finite tensor realization.
The comparison is the descended balanced tensor map with the coefficient counits,
not an independently chosen isomorphism at each space.

Source: fix-prop-projection-formula.proof.md, same projection map.
(blueprint: new-sf-finite-intrinsic-projection-compatibility).

Proof: compare the actual proper counit factor and the open tensor/compositor
factor separately, through their explicitly constructed intermediate coordinate
comparison. Paste the two equations. The constructible component is, by definition,
the fixed proper/open word conjugated by sourceComparison and targetComparison. -/
theorem finiteIntrinsicProjectionCompatibility
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ)
    (S : SixFunctorFiniteOperations D C E (m + 1) (Nat.le_add_left 1 m)) :
      ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        (c : Compactification f.hom.left)
        (K : sixFunctorFiniteCategory D C E (m + 1) (Nat.le_add_left 1 m) X)
        (L : finiteTorConstructibleCategory C.l E (m + 1)
          (Nat.le_add_left 1 m) Y.obj.left)
        (U : normalizedDVRDerived C.l E X.obj.left m)
        (V : normalizedDVRDerived C.l E Y.obj.left m)
        (k : U ≅ K.obj) (l : V ≅ L.obj),
        SystemProjectionFormula.finiteProjection C.l E D C.different c
            X.obj.hom Y.obj.hom m U V ≫
          (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).map
            ((canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m X).hom.app
              (U, (finiteDerivedPullback C.l E m f.hom.left).obj V) ≫
              (evaluatedTensor (C := C) (E := E) m X).map
                (Prod.mkHom k.hom
                  ((finiteDerivedPullback C.l E m f.hom.left).map l.hom ≫
                    (S.finitePullback f).inv.app ⟨L.obj, L.property.1⟩))) ≫
          (S.finiteSupport f c).inv.app
            (((CompactSupportFiniteProjection.partialTensor S X).obj K).obj
              ((CompactSupportFiniteProjection.torPull S f).obj L)) =
        (canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Y).hom.app
            ((sixFunctorFiniteSupport D C E (m + 1)
              (Nat.le_add_left 1 m) f c).obj U, V) ≫
          (evaluatedTensor (C := C) (E := E) m Y).map
            (Prod.mkHom
              ((sixFunctorFiniteSupport D C E (m + 1)
                (Nat.le_add_left 1 m) f c).map k.hom ≫
                (S.finiteSupport f c).inv.app K) l.hom) ≫
          (finiteInclusion (C := C) (E := E) m Y).map
            (CompactSupportFiniteProjection.component S f c K L) := by
  intro X Y f c K L U V k l
  have h := paste_factors
    (finiteIntrinsicProjectionProperFactor m S f c K L U V k l)
    (finiteIntrinsicProjectionOpenFactor m S f c K L U V k l)
  have hc := FiniteIntrinsicProjectionCoordinates.component_factorization m S f c K L
  have result := h.trans (congrArg
    (fun q ↦ ((canonicalFiniteIntrinsicTensorComparison (C := C) (E := E) m Y).hom.app
        ((sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).obj U, V) ≫
      (evaluatedTensor (C := C) (E := E) m Y).map
        (Prod.mkHom ((sixFunctorFiniteSupport D C E (m + 1)
          (Nat.le_add_left 1 m) f c).map k.hom ≫
            (S.finiteSupport f c).inv.app K) l.hom)) ≫ q) hc.symm)
  delta SystemProjectionFormula.finiteProjection
  have final := reassociate_words result
  run_tac Lean.Elab.Tactic.withMainContext do
    let some r := (← Lean.getLCtx).findFromUserName? `final |
      throwError "missing pasted factorization"
    let g ← Lean.Elab.Tactic.getMainGoal
    let src ← Lean.Meta.inferType r.toExpr
    let tgt ← g.getType
    let v ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq src tgt)
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[v, r.toExpr])
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    coefficientInstanceCongr cache 100 v.mvarId!
    Lean.Elab.Tactic.replaceMainGoal []

end WeilConjectures.IntegralProjectionReduction
