/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition
public import Sheaf.AlgebraicGeometry.HigherDirectImageTransitionIsIsoOfLower
import Sheaf.AlgebraicGeometry.EtalePullbackSingleComp

/-! # Single-complex normalization of target transitions

Source: Stacks Project Tags 0F07 and 09Z1.
(blueprint: lem-sbc-target-transition-higher-image)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] lowerStarPlusTransition

variable (Λ : Type (u + 1)) [CommRing Λ]

private lemma normalize_transition
    {C D B V : Type*} [Category C] [Category D] [Category B] [Category V]
    (R : C ⥤ B) (R' : D ⥤ B) (A : C ⥤ D) (H : B ⥤ V)
    {K L : C} {M₁ M₂ M N P Q Z : D}
    (t : R.obj K ⟶ R'.obj (A.obj K)) (t' : R.obj L ⟶ R'.obj (A.obj L))
    (c : K ⟶ L) (d₁ : A.obj K ⟶ M₁) (d₂ : M₁ ⟶ M₂)
    (d₃ : M₂ ⟶ M) (d₄ : M ⟶ N) (m : N ⟶ P) (j : P ⟶ Z)
    (u : A.obj L ⟶ Q) (δ : Q ⟶ Z)
    (hn : R.map c ≫ t' = t ≫ R'.map (A.map c))
    (hc : d₁ ≫ d₂ ≫ d₃ ≫ d₄ ≫ m ≫ j = A.map c ≫ u ≫ δ) :
    H.map (t ≫ R'.map (d₁ ≫ d₂ ≫ d₃ ≫ d₄)) ≫
        H.map (R'.map m) ≫ H.map (R'.map j) =
      H.map (R.map c) ≫ H.map (t' ≫ R'.map u) ≫ H.map (R'.map δ) := by
  simp only [← H.map_comp]
  congr 1
  simp only [Category.assoc, ← R'.map_comp]
  rw [hc]
  simp only [R'.map_comp]
  rw [← reassoc_of% hn]

private lemma lower_transition_naturality
    {X Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ X) (h' : Y' ⟶ X)
    (w : a ≫ h = h')
    {K L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (f : K ⟶ L) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).map f ≫
        lowerStarPlusTransition Λ a h h' w L =
      lowerStarPlusTransition Λ a h h' w K ≫
        R+((h')_*[ModuleCat.{u + 1} Λ]).map
          (D+((a)^*[ModuleCat.{u + 1} Λ]).map f) := by
  let sq : CommSq a h' h (𝟙 X) := ⟨by rw [w, Category.comp_id]⟩
  have hn := ((Functor.whiskerLeft R+((h)_*[ModuleCat.{u + 1} Λ])
    (upperStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv) ≫
      baseChange (ModuleCat.{u + 1} Λ) sq).naturality f
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_map,
    Functor.id_map] at hn
  rw [lowerStarPlusTransition_eq_baseChange Λ a h h' w sq K,
    lowerStarPlusTransition_eq_baseChange Λ a h h' w sq L]
  exact hn

private lemma forward_of_inverse
    {C : Type*} [Category C] {K L M N P : C}
    (i : K ≅ L) (c : L ⟶ M) (d : M ⟶ N) (j : P ≅ N) (v : K ⟶ P)
    (h : c ≫ d ≫ j.inv = i.inv ≫ v) : i.hom ≫ c ≫ d = v ≫ j.hom := by
  rw [← cancel_epi i.inv, ← cancel_mono j.inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  exact h

private lemma coefficient_single_map
    {T Y T' Y' : Scheme.{u}} (e : Y ⟶ T) (π : T' ⟶ T)
    (a : Y' ⟶ Y) (e' : Y' ⟶ T') (wa : a ≫ e = e' ≫ π)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : ((π)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ F') :
    (upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      eqToHom (by rw [wa]) ≫
      (upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      D+((e')^*[ModuleCat.{u + 1} Λ]).map
        ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      D+((e')^*[ModuleCat.{u + 1} Λ]).map
        ((DerivedCategory.Plus.singleFunctor _ 0).map f) ≫
      ((((e')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F') =
    D+((a)^*[ModuleCat.{u + 1} Λ]).map
        ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      ((((a)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((e)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) a e).inv.app F ≫
          (upperStarComp (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).hom.app F ≫
          ((e')^*[ModuleCat.{u + 1} Λ]).map f) := by
  have hn :=
    (((e')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  have hf : eqToHom (by rw [wa]; rfl) ≫
      (upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
      D+((e')^*[ModuleCat.{u + 1} Λ]).map
        ((((π)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
      ((((e')^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (((π)^*[ModuleCat.{u + 1} Λ]).obj F)) =
      ((((a ≫ e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F) ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).hom.app F) := by
    generalize hk : a ≫ e = k at wa ⊢
    subst wa
    simp only [eqToHom_refl, Category.id_comp]
    exact forward_of_inverse
      ((upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) _ _
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
        ((upperStarComp (ModuleCat.{u + 1} Λ) e' π).app F)) _
      (upperStarPlusComp_single Λ e' π F)
  rw [reassoc_of% hf]
  simp only [Functor.map_comp]
  rw [reassoc_of% (upperStarPlusComp_single Λ a e F)]

/-- Normalize a target transition as a higher-image transition with an underived coefficient map.

Source: Stacks Project Tag 0F07, coefficient identification preceding condition (2),
and Tag 09Z1, canonical restriction maps.
(blueprint: lem-sbc-target-transition-higher-image)

Proof: Expand the target transition before homology and the two instances of
baseChangeTargetFunctorIso. Naturality of the lower-star triangle transition moves
its source single-complex comparison to the target. The composition law for exact
pullbacks on single complexes identifies the two derived composition comparisons
with singleFunctor applied to the underived square comparison. Transport along wa
is respected by functoriality and proof irrelevance. The remaining target
single-complex comparison is the targetFunctorIso prefix. Apply Rh'_* and degree-q
homology, which preserve composition. Identity arrows and zero sheaves satisfy the
same identities; no sign or finiteness assumption on q is used. -/
theorem baseChangeTargetTransition_higherImage
    {X T Y T' Y' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (π : T' ⟶ T) (a : Y' ⟶ Y) (e' : Y' ⟶ T') (h' : Y' ⟶ X)
    (wa : a ≫ e = e' ≫ π) (wh : a ≫ h = h')
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F' : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : ((π)^*[ModuleCat.{u + 1} Λ]).obj F ⟶ F') :
    baseChangeTargetTransition Λ e h q π a e' h' wa wh F ≫
      (baseChangeTargetFunctor Λ e' h' q).map f ≫
      (baseChangeTargetFunctorHigherImageIso Λ e' h' q F').hom =
    (baseChangeTargetFunctorHigherImageIso Λ e h q F).hom ≫
      higherDirectImageTransition Λ a h h' wh q (((e)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
      higherDirectImageMap Λ h' q
        ((upperStarComp (ModuleCat.{u + 1} Λ) a e).inv.app F ≫
          (upperStarComp (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).hom.app F ≫
          ((e')^*[ModuleCat.{u + 1} Λ]).map f) := by
  have hn := lower_transition_naturality Λ a h h' wh
    ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
  have hc := coefficient_single_map Λ e π a e' wa F F' f
  dsimp only [Functor.comp_obj] at hn hc
  dsimp only [baseChangeTargetFunctor, Functor.comp_map, baseChangeTargetTransition,
    baseChangeTargetFunctorHigherImageIso, higherDirectImageTransition, higherDirectImageMap,
    Functor.mapIso_hom, Iso.app_hom, Functor.comp_obj, higherDirectImage]
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let getLocal (n : Lean.Name) := do
        return (← Lean.Meta.getLocalDeclFromUserName n).toExpr
      let hn ← getLocal `hn
      let hc ← getLocal `hc
      let sides (h : Lean.Expr) : Lean.MetaM (Lean.Expr × Lean.Expr) := do
        let type ← Lean.instantiateMVars (← Lean.Meta.inferType h)
        let some (_, lhs, rhs) := type.consumeMData.eq? |
          throwError "expected equality"
        return (lhs, rhs)
      let split (e : Lean.Expr) := do
        let e := e.consumeMData
        let a := e.getAppArgs
        unless e.isAppOf ``CategoryTheory.CategoryStruct.comp do
          throwError "expected composition"
        return (a[a.size - 2]!, a.back!)
      let (nl, nr) ← sides hn
      let (rc, t') ← split nl
      let (t, rac) ← split nr
      let ra := rc.getAppArgs
      let rap := rac.getAppArgs
      let ac := rap.back!
      let aa := ac.getAppArgs
      let (cl, cr) ← sides hc
      let (d₁, tail) ← split cl
      let (d₂, tail) ← split tail
      let (d₃, tail) ← split tail
      let (d₄, tail) ← split tail
      let (m, j) ← split tail
      let (_, tail) ← split cr
      let (u, δ) ← split tail
      let type ← Lean.instantiateMVars (← goal.getType)
      let some (_, lhs, _) := type.consumeMData.eq? | throwError "expected equality"
      let (ht, _) ← split lhs
      let ha := ht.getAppArgs
      let endpoints (f : Lean.Expr) := do
        let a := (← Lean.Meta.inferType f).getAppArgs
        return (a[a.size - 2]!, a.back!)
      let (K, L) ← endpoints ra.back!
      let (_, M₁) ← endpoints d₁
      let (_, M₂) ← endpoints d₂
      let (_, M) ← endpoints d₃
      let (_, N) ← endpoints d₄
      let (_, P) ← endpoints m
      let (_, Z) ← endpoints j
      let (_, Q) ← endpoints u
      let args := #[ra[0]!, aa[2]!, ra[2]!, ha[2]!,
        ra[1]!, aa[3]!, ra[3]!, ha[3]!,
        ra[4]!, rap[4]!, aa[4]!, ha[4]!, K, L, M₁, M₂, M, N, P, Q, Z,
        t, t', ra.back!, d₁, d₂, d₃, d₄, m, j, u, δ, hn, hc]
      let decl ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo (← `(normalize_transition))
      let info ← Lean.getConstInfo decl
      let mut levelMap : Std.HashMap Lean.Name Lean.Level := {}
      let mut type := info.type
      for i in [:8] do
        let .forallE _ domain body _ := type | throwError "expected parameter"
        if let .sort (.succ (.param n)) := domain then
          let some l := (← Lean.Meta.getLevel args[i]!).dec |
            throwError "expected object type"
          levelMap := levelMap.insert n l
        else
          let expected := domain.getAppFn.constLevels!
          let actual := (← Lean.Meta.inferType args[i]!).getAppFn.constLevels!
          for (e, a) in expected.zip actual do
            if let .param n := e then levelMap := levelMap.insert n a
        type := body.instantiate1 args[i]!
      let levels := info.levelParams.map fun n => (levelMap.get? n).get!
      let proof := Lean.mkAppN (Lean.mkConst decl levels) args
      let proofType ← Lean.Meta.inferType proof
      let added ← goal.assert `hm proofType proof
      let (_, added) ← added.intro `hm
      Lean.Elab.Tactic.replaceMainGoal [added]
      Lean.Elab.Tactic.evalTactic (← `(tactic| bc_structural_exact $(Lean.mkIdent `hm):ident))

end AlgebraicGeometry.Etale
