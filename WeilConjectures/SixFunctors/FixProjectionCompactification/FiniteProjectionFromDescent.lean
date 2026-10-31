/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionCompactificationData
public import WeilConjectures.SixFunctors.ProjectionRefinementDescent.ProjectionRefinementDescent
import Mathlib.Lean.Meta.CongrTheorems

/-! A finite projection square assembled from the refinement-law clause.

This is an intermediate statement for
`WeilConjectures.SixFunctors.FixProjectionCompactification.FiniteProjectionCompactificationSquare`.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace WeilConjectures.FixProjectionCompactification

/- The native law and the generic coefficient wrappers select definitionally equal
ring instances through different paths. Comparing the entire derived construction
by reflexivity unfolds too much. Build congruence at each argument boundary and
cache repeated equality proofs; the kernel checks the resulting proof normally. -/
private meta def strictInstanceCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
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
      let a := a.consumeMData
      let b := b.consumeMData
      let a ← match a with
        | .letE .. => Lean.Meta.whnf a
        | _ => if a.getAppFn.isConstOf ``AlgebraicGeometry.ProEtale.ProperOpenDerived then
            Lean.Meta.whnf a else pure a
      let b ← match b with
        | .letE .. => Lean.Meta.whnf b
        | _ => if b.getAppFn.isConstOf ``AlgebraicGeometry.ProEtale.ProperOpenDerived then
            Lean.Meta.whnf b else pure b
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else if ← g.proofIrrelHeq then pure ()
      else if a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
        let f := a.getAppFn
        let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
        let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
        let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
          (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
        let gs ← g.apply (c.proof.beta #[f]) { synthAssignedInstances := false }
        for g in gs do strictInstanceCongr cache fuel g
      else
        if t.isHEq then g.hrefl else g.refl
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)

attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  ProjectionRefinementDescent.tensorInput

attribute [local irreducible] Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  projectionMapOfCompactification
  AlgebraicGeometry.ProEtale.derivedTensor
  refinementFixedObject refinementComparisonAtWitness

private theorem transport_common
    {A : Type*} [Category A] {B : Type*} [Category B]
    (F G H : A ⥤ B) {a b : A} (e : a ≅ b)
    (s : F.obj a ≅ G.obj a) (t : F.obj a ≅ H.obj a) :
    (F.mapIso e.symm ≪≫ s ≪≫ G.mapIso e).symm ≪≫
        (F.mapIso e.symm ≪≫ t ≪≫ H.mapIso e) =
      G.mapIso e.symm ≪≫ s.symm ≪≫ t ≪≫ H.mapIso e := by
  ext
  simp

private theorem descend_square
    {A : Type*} [Category A] {B : Type*} [Category B]
    (F : A ⥤ B) {a b c : A} {x y z : B}
    (s : a ≅ b) (t : a ≅ c) (v : x ≅ y) (w : x ≅ z)
    (p : F.obj a ⟶ x) (q : F.obj b ⟶ y) (r : F.obj c ⟶ z)
    (hq : p ≫ v.hom = F.map s.hom ≫ q)
    (hr : p ≫ w.hom = F.map t.hom ≫ r) :
    q ≫ (v.symm ≪≫ w).hom = F.map (s.symm ≪≫ t).hom ≫ r := by
  apply (cancel_epi (F.map s.hom)).mp
  calc
    F.map s.hom ≫ (q ≫ (v.symm ≪≫ w).hom) = p ≫ w.hom := by
      rw [← Category.assoc, ← hq]
      simp
    _ = F.map t.hom ≫ r := hr
    _ = F.map s.hom ≫ (F.map (s.symm ≪≫ t).hom ≫ r) := by
      simp [← CategoryTheory.Functor.map_comp, ← Category.assoc]

private theorem descend_transported_square
    {A : Type*} [Category A] {B : Type*} [Category B]
    (F G H : A ⥤ B) (T : B ⥤ B) {k a b : A} (e : a ≅ b)
    (sK : F.obj k ≅ G.obj k) (tK : F.obj k ≅ H.obj k)
    (sT : F.obj a ≅ G.obj a) (tT : F.obj a ≅ H.obj a)
    (p : T.obj (F.obj k) ⟶ F.obj b)
    (q : T.obj (G.obj k) ⟶ G.obj b)
    (r : T.obj (H.obj k) ⟶ H.obj b)
    (hq : p ≫ (F.mapIso e.symm ≪≫ sT ≪≫ G.mapIso e).hom =
      T.map (F.mapIso (Iso.refl k).symm ≪≫ sK ≪≫ G.mapIso (Iso.refl k)).hom ≫ q)
    (hr : p ≫ (F.mapIso e.symm ≪≫ tT ≪≫ H.mapIso e).hom =
      T.map (F.mapIso (Iso.refl k).symm ≪≫ tK ≪≫ H.mapIso (Iso.refl k)).hom ≫ r) :
    q ≫ (G.mapIso e.symm ≪≫ sT.symm ≪≫ tT ≪≫ H.mapIso e).hom =
      T.map (sK.symm ≪≫ tK).hom ≫ r := by
  simp only [Iso.refl_symm, Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl] at hq hr
  have result := descend_square T sK tK
    (F.mapIso e.symm ≪≫ sT ≪≫ G.mapIso e)
    (F.mapIso e.symm ≪≫ tT ≪≫ H.mapIso e) p q r hq hr
  rw [transport_common] at result
  exact result

private theorem coefficient_assembly
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (b c d : Compactification f)
    (K : ProperOpenDerived A X) (L : ProperOpenDerived A Y)
    (T : ProperOpenDerived A X)
    (e : T ≅ ((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj
      ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj L))
    (sK : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b).obj K ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K)
    (tK : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b).obj K ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj K)
    (sT : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b).obj T ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj T)
    (tT : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b).obj T ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj T)
    (hq : ProjectionRefinementDescent.coefficientProjectionComponent A b K L ≫
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b).mapIso e.symm ≪≫ sT ≪≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso e).hom =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b).mapIso
            (Iso.refl K).symm ≪≫
          sK ≪≫ (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso
            (Iso.refl K)).hom).app L ≫
        ProjectionRefinementDescent.coefficientProjectionComponent A c K L)
    (hr : ProjectionRefinementDescent.coefficientProjectionComponent A b K L ≫
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b).mapIso e.symm ≪≫ tT ≪≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso e).hom =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b).mapIso
            (Iso.refl K).symm ≪≫
          tK ≪≫ (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
            (Iso.refl K)).hom).app L ≫
        ProjectionRefinementDescent.coefficientProjectionComponent A d K L) :
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).app L ≫
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso e.symm ≪≫
          sT.symm ≪≫ tT ≪≫
            (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso e).hom =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map (sK.symm ≪≫ tK).hom).app L ≫
        ((projectionMapOfCompactification (ModuleCat.{u + 1} A) d).app K).app L := by
  exact descend_transported_square
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) b)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    ((derivedTensor (ModuleCat.{u + 1} A) Y).flip.obj L) e sK tK sT tT
    (ProjectionRefinementDescent.coefficientProjectionComponent A b K L)
    (ProjectionRefinementDescent.coefficientProjectionComponent A c K L)
    (ProjectionRefinementDescent.coefficientProjectionComponent A d K L) hq hr

private theorem theta_finite_eq
    (K₀ : Type u) [Field K₀] (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n + 1) (hl : IsUnit (l : K₀))
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (K : ProperOpenDerived (ProjectionRefinementDescent.Coefficient l E n) X)
    (O : RefinementFiniteLevelOrigin l E (n + 1) hn X)
    (e : refinementFiniteLevelFixedObject l E (n + 1) hn X O ≅ K) :
    ProjectionRefinementDescent.theta l E n r K O e =
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ProjectionRefinementDescent.Coefficient l E n)) c).mapIso e.symm ≪≫
        refinementComparisonIsomorphism K₀ l hl E (n + 1) hn f r O ≪≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ProjectionRefinementDescent.Coefficient l E n)) d).mapIso e := by
  rfl

attribute [local irreducible] ProjectionRefinementDescent.theta
  refinementComparisonIsomorphism

/-- The refinement-law clause of finite descent implies the finite projection square.

Source: the compactification-independence sentence of
`prop-sf-pf-coherence.proof.md` (blueprint:
`lem-sf-finite-projection-compactification-square`).

Proof: instantiate the refinement law on both arrows from a common refinement, apply
it to the retained origin presentations, and cancel the comparison isomorphisms.
Transport the two retained target presentations through the common source; the
identity witness maps cancel by functoriality. The resulting composites are exactly
the two rho maps in `finiteLaw`. This is a genuine intermediate assembly statement:
it assumes only the refinement-law clause and supplies the whole finite coefficient
law to the parent theorem.
(blueprint: lem-sf-finite-projection-compactification-square-specialization).
-/
theorem finiteProjectionFromDescent
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n + 1)
    (S : SixFunctorOperationDatum D C E (n + 1) hn)
    (hl : IsUnit (C.l : D.k))
    (h : ∀ {X Y : Scheme.{u}}
      [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
      [QuasiCompact (X ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
      [QuasiCompact (Y ↘ Spec (.of D.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
      ∀ (c d : Compactification f) (r : c.Refinement d)
        (K : (ProjectionRefinementDescent.boundedConstructible C.l E n X).FullSubcategory)
        (L : (ProjectionRefinementDescent.finiteTor C.l E n Y).FullSubcategory),
        ProjectionRefinementDescent.refinementLaw C.l E n c d r K L) :
    finiteLaw D C E (n + 1) hn hl := by
  let _operationDatum := S
  intro X Y _ _ _ _ _ _ f _ _ _ _ c₁ c₂ d r₁ r₂ O L OT
  dsimp only
  intro e hK hL
  have h₁ := h f d c₁ r₁
    ⟨refinementFiniteLevelFixedObject C.l E (n + 1) hn X O, hK⟩ ⟨L, hL⟩
    O (Iso.refl _) OT e
  have h₂ := h f d c₂ r₂
    ⟨refinementFiniteLevelFixedObject C.l E (n + 1) hn X O, hK⟩ ⟨L, hL⟩
    O (Iso.refl _) OT e
  simp only [theta_finite_eq D.k C.l E n hn hl f] at h₁ h₂
  have result := coefficient_assembly
    (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E (n + 1))) d c₁ c₂
    (refinementFiniteLevelFixedObject C.l E (n + 1) hn X O) L
    (refinementFiniteLevelFixedObject C.l E (n + 1) hn X OT) e
    (refinementComparisonIsomorphism D.k C.l hl E (n + 1) hn f r₁ O)
    (refinementComparisonIsomorphism D.k C.l hl E (n + 1) hn f r₂ O)
    (refinementComparisonIsomorphism D.k C.l hl E (n + 1) hn f r₁ OT)
    (refinementComparisonIsomorphism D.k C.l hl E (n + 1) hn f r₂ OT)
    h₁ h₂
  run_tac Lean.Elab.Tactic.withMainContext do
    let some r := (← Lean.getLCtx).findFromUserName? `result |
      throwError "missing result"
    let g ← Lean.Elab.Tactic.getMainGoal
    let src ← Lean.Meta.inferType r.toExpr
    let tgt ← g.getType
    let v ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq src tgt)
    g.assign (← Lean.Meta.mkAppM ``Eq.mp #[v, r.toExpr])
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    strictInstanceCongr cache 100 v.mvarId!
    Lean.Elab.Tactic.replaceMainGoal []

end WeilConjectures.FixProjectionCompactification
