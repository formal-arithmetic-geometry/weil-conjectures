/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffinePullbackCoefficientMap
public import Sheaf.AlgebraicGeometry.CoherentEtalePullbackData
import all Sheaf.AlgebraicGeometry.CoherentEtaleRestrictionComposition
import Mathlib.Lean.Meta.CongrTheorems
import Sheaf.AlgebraicGeometry.SheafHDerivedPullback
import Sheaf.AlgebraicGeometry.UnitCoherentRawEvaluationFormulaAux
import Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization

/-! # Raw evaluation with the typed structural pullback map -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/- Construct the presentation conversion by congruence, caching repeated subproofs.
Normalize composed functor objects before decomposing their dependent arguments. -/
private meta def sectionCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr)) :
    Nat → Lean.MVarId → Lean.MetaM Unit
  | 0, g => Lean.Meta.withDefault g.hrefl
  | n + 1, g => g.withContext do
    let g ← Lean.Meta.withReducible g.eqOfHEq
    let ty ← Lean.Meta.withReducible g.getType'
    if let some pf := (← cache.get)[ty]? then
      g.assign pf
      return
    if ty.isForall then
      let (_, g) ← g.intro1
      sectionCongr cache n g
      return
    let some (_, lhs, _, rhs) := ty.heq? |
      throwError "strict congruence expected HEq, got {ty}"
    for (tp, pf) in (← cache.get).toArray do
      if let some (_, l, _, r) := tp.heq? then
        if lhs == l && rhs == r then
          g.assign pf
          return
    let solve : Lean.MetaM Unit := do
      if lhs == rhs then
        Lean.Meta.withDefault g.hrefl
      else if ← Lean.Meta.isProof lhs then
        let pf ← Lean.Meta.mkConstWithFreshMVarLevels ``proof_irrel_heq
        let gs ← Lean.Meta.withDefault (g.apply pf)
        for h in gs do sectionCongr cache n h
      else if lhs.isApp && rhs.isApp && lhs.getAppFn == rhs.getAppFn then
        let f := lhs.getAppFn
        if f.isConstOf ``Functor.obj then
          let lhs' ← Lean.Meta.withReducible (Lean.Meta.whnf lhs)
          let rhs' ← Lean.Meta.withReducible (Lean.Meta.whnf rhs)
          if lhs' != lhs || rhs' != rhs then
            let g ← g.change (← Lean.Meta.mkHEq lhs' rhs')
            sectionCongr cache n g
            return
        let info ← Lean.Meta.getFunInfoNArgs f lhs.getAppNumArgs
        let cthm ← Lean.Meta.mkRichHCongr (forceHEq := true)
          (← Lean.Meta.inferType f) info (fixedFun := true) (fixedParams := #[])
        let pf := cthm.proof.beta #[f]
        let gs ← Lean.Meta.withDefault
          (g.apply pf { synthAssignedInstances := false })
        for h in gs do sectionCongr cache n h
      else
        let lhs' ← Lean.Meta.withReducible (Lean.Meta.whnf lhs)
        let rhs' ← Lean.Meta.withReducible (Lean.Meta.whnf rhs)
        if lhs' != lhs || rhs' != rhs then
          let g ← g.change (← Lean.Meta.mkHEq lhs' rhs')
          sectionCongr cache n g
        else
          let tp ← Lean.Meta.inferType lhs
          if tp.getAppFn.isConstOf ``AlgebraicGeometry.Scheme then
            let g ← Lean.Meta.withReducible g.heqOfEq
            let projectionProof ← Lean.Meta.mkConstWithFreshMVarLevels
              ``CategoryTheory.MorphismProperty.Over.pullback_obj_left
            let gs ← Lean.Meta.withDefault (g.apply projectionProof)
            for h in gs do sectionCongr cache n h
          else
            Lean.Meta.withDefault g.hrefl
    solve
    let pf ← Lean.instantiateMVars (Lean.mkMVar g)
    cache.modify (·.insert ty pf)


noncomputable section
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
set_option autoImplicit false
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange
attribute [local irreducible] tensorPullback tensorPullbackObj tensorSectionsComp
  tensorSectionsUnit qcoherentPullbackSection affineRealizationRawEvaluation
  CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.comp
  CategoryTheory.Abelian.Ext.instAddCommGroup
  CategoryTheory.Functor.rightDerived CategoryTheory.Functor.rightDerivedFunctor
  Etale.cohomologyMap CategoryTheory.Sheaf.H.map CategoryTheory.Adjunction.homEquiv
  Etale.upperStar Etale.cohomology coherentEtaleRestrictionIso
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived CategoryTheory.derivedExtEvaluation
  affineRealizationRawEquiv Etale.rawRestrictedCohomologyComparison
  Etale.rawAffineComplexPullback
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

private theorem cohomologyComposition_congr {X Y Z : Scheme.{u}}
    (b b' : Z ⟶ Y) (j : Y ⟶ X) (k : Z ⟶ X)
    (w : b ≫ j = k) (w' : b' ≫ j = k) (h : b = b')
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj F) q) :
    Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} b j k w.symm).inv.app F)
      q (Etale.cohomologyMap b ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj F) q x) =
    Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} b' j k w'.symm).inv.app F)
      q (Etale.cohomologyMap b' ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj F) q x) := by
  subst b'
  rfl

set_option backward.isDefEq.respectTransparency.types true in
private theorem typedRestrictionComposition {X Y Z : Scheme.{u}}
    (b : Z ⟶ Y) (j : Y ⟶ X) [AlgebraicGeometry.Etale b] [AlgebraicGeometry.Etale j]
    (k : Z ⟶ X) (w : b ≫ j = k) [AlgebraicGeometry.Etale k]
    (G : X.Modules) [G.IsQuasicoherent]
    (θ : liftedCoherentEtaleSheaf ((tensorPullback j).obj G) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} b).obj
        (liftedCoherentEtaleSheaf ((tensorPullback k).obj G)))
    (hθ : HasQcoherentPullbackSectionFormula b ((tensorPullback j).obj G)
      ((tensorPullback k).obj G) (tensorCompositeCoefficientMap b j k w G) θ) :
    (Etale.upperStar AddCommGrpCat.{u + 1} b).map
        (coherentEtaleRestrictionIso j G).hom ≫
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b).homEquiv
        _ _).symm θ =
    (Etale.upperStarComp AddCommGrpCat.{u + 1} b j k w.symm).inv.app
      (liftedCoherentEtaleSheaf G) ≫ (coherentEtaleRestrictionIso k G).hom := by
  have hψ := tensorCompositeCoefficientMap_eq b j k w G
  have hs := (hasQcoherentPullbackSectionFormula_congr b ((tensorPullback j).obj G)
    ((tensorPullback k).obj G) _ _ hψ θ hθ).app
  apply restrictionComposition b j k w G θ
  intro U s
  refine Eq.mp ?_ (hs U s)
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let g ← Lean.Elab.Tactic.getMainGoal
      let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
      sectionCongr cache 60 g
      Lean.Elab.Tactic.replaceMainGoal []

/-- Raw evaluation carries chart restriction to the constructed structural pullback.
Source: Stacks Project, Tags 03Q8, 03FD and 03DR.
(blueprint: lem-weil-pbc-affine-raw-evaluation-typed-pullback).
Proof: expand the constructed coefficient map by its composition equation. On
variable schemes, explicit cached congruence gives the section premise of the
proved generic restrictionComposition lemma. Its conclusion identifies the
adjunct coefficient map with inverse-image composition and the coherent
restriction isomorphisms. Specialize this square to the actual fibre products.
Naturality of rawRestrictedClassNormalization and the restriction equation for
sheafHDerivedEquiv give the derived restriction square. The two chart maps agree
by definition; a generic equality-substitution lemma transports their composites.
Rewrite both raw evaluations by unit_coherent_raw_evaluation_formula. Functoriality
of Sheaf.H.map, the coefficient square, and naturality of cohomologyMap identify
the result with coherentEtalePullbackMap_apply. No ordinary coherent comparison
or additional geometric assumption enters. Empty charts, zero modules, identity
arrows and degree zero use exactly the same equations. -/
theorem affineRealizationRawEvaluation_typed_pullback {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (V V' : S.Etale) (h : V' ⟶ V)
    (θ : liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} (affineRealizationChartMap f h)).obj
        (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V')))
    (hθ : HasQcoherentPullbackSectionFormula (affineRealizationChartMap f h)
      (affineRealizationCoefficient f G V) (affineRealizationCoefficient f G V')
      (affineRealizationCoefficientMap f G h) θ)
    (q : ℕ)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V)) :
    affineRealizationRawEvaluation f G q V'
      ((Etale.abelianHigherDirectImageRawPresheaf f q
        (liftedCoherentEtaleSheaf G)).map h.op z) =
      coherentEtalePullbackMap (affineRealizationChartMap f h)
        (affineRealizationCoefficient f G V) (affineRealizationCoefficient f G V') θ q
        (affineRealizationRawEvaluation f G q V z) := by
  have hθ' := hasQcoherentPullbackSectionFormula_congr (affineRealizationChartMap f h)
    (affineRealizationCoefficient f G V) (affineRealizationCoefficient f G V')
    _ _ (affineRealizationCoefficientMap_eq f G h) θ hθ
  have hm := coherentEtalePullbackMap_apply (affineRealizationChartMap f h)
    (affineRealizationCoefficient f G V) (affineRealizationCoefficient f G V') θ q
    (affineRealizationRawEvaluation f G q V z)
  have hw := affineRealizationChartMap_w f h
  let F := liftedCoherentEtaleSheaf G
  let b := affineRealizationChartMap f h
  have : AlgebraicGeometry.Etale (b ≫ pullback.snd V.hom f) := by
    rw [hw]
    infer_instance
  have : AlgebraicGeometry.Etale b :=
    AlgebraicGeometry.Etale.of_comp b (pullback.snd V.hom f)
  let A := (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd V.hom f)).obj F
  let A' := (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.snd V'.hom f)).obj F
  let e := coherentEtaleRestrictionIso (pullback.snd V.hom f) G
  let e' := coherentEtaleRestrictionIso (pullback.snd V'.hom f) G
  let c := (Etale.upperStarComp AddCommGrpCat.{u + 1} b
    (pullback.snd V.hom f) (pullback.snd V'.hom f)
    hw.symm).inv.app F
  let a := ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b).homEquiv
    _ _).symm θ
  let r := (Etale.sheafHDerivedEquiv A q).symm
    (Etale.rawRestrictedCohomologyComparison f q F V z)
  have hcoeff := typedRestrictionComposition
    (X := X) (Y := Limits.pullback V.hom f) (Z := Limits.pullback V'.hom f)
    b (pullback.snd V.hom f) (pullback.snd V'.hom f)
    hw G θ hθ'
  have hnorm := Etale.rawRestrictedClassNormalization f q F
  obtain ⟨k, hk⟩ := hnorm.1
  have hnmap := k.hom.naturality h.op
  rw [hk V', hk V, hnorm.2.1 V V' h] at hnmap
  have hn := ConcreteCategory.congr_hom hnmap z
  have hp := (congrArg (Etale.sheafHDerivedEquiv A' q).symm hn).trans
    (Etale.sheafHDerivedEquiv_symm_restriction f q F V V' h _)
  have hb : Etale.normalizationChartMap f h = b := by
    unfold b affineRealizationChartMap Etale.normalizationChartMap
    rfl
  have hwN : Etale.normalizationChartMap f h ≫ pullback.snd V.hom f =
      pullback.snd V'.hom f := by
    rw [hb]
    exact hw
  have hp' := hp.trans (cohomologyComposition_congr
    (Etale.normalizationChartMap f h) b (pullback.snd V.hom f)
    (pullback.snd V'.hom f) hwN hw hb F q
    ((Etale.sheafHDerivedEquiv A q).symm
      (Etale.rawRestrictedCohomologyComparison f q F V z)))
  refine Eq.trans ?_ hm.symm
  rw [unit_coherent_raw_evaluation_formula, unit_coherent_raw_evaluation_formula]
  refine (congrArg (Sheaf.H.map e'.hom q) hp').trans ?_
  calc
    _ = Sheaf.H.map (c ≫ e'.hom) q (Etale.cohomologyMap b A q r) :=
      (Sheaf.H.map_comp_apply c e'.hom _).symm
    _ = Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} b).map e.hom ≫ a)
        q (Etale.cohomologyMap b A q r) := congrArg (fun t ↦
          Sheaf.H.map t q (Etale.cohomologyMap b A q r)) hcoeff.symm
    _ = _ := (Sheaf.H.map_comp_apply _ a _).trans
      (congrArg (Sheaf.H.map a q) (Etale.cohomologyMap_map b q e.hom r).symm)

end
end AlgebraicGeometry.Scheme.Modules
