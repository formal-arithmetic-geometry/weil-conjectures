/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.ComponentExchangeFactor

/-!

# The exchange `ν_c` of the support on pushforwards from a component, without hypothesis

The ambient hypothesis `hC` of `supportCompactSupportExchange_app_lowerStar` is an instance of
`NearbyCyclesModel.Hom.compactSupportExchange_comp_app`
(`Correspondence.IsContractingAt.supportCompactSupportExchange_app_lowerStar_ambient`), after the
`Precoherent Profinite` proofs inside the `MonObj` instances of the goal are identified by the
tactic `normalize_precoherent` (the normalizer of `PointExchangeOnComponentBdc`, as a tactic).
This gives `supportCompactSupportExchange_app_lowerStar_eq`, input `hF1` of
`CategoryTheory.supportIdentity_aux`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Replace, inside the `MonObj` instances `Sheaf.monObj_sheafCompose_obj` of the goal, every
`Precoherent Profinite` proof by the first one found (see `PointExchangeOnComponentBdc`). -/
elab "normalize_precoherent" : tactic => do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← Lean.Meta.whnfR (← Lean.instantiateMVars (← goal.getType))
    let isInst (e : Lean.Expr) : Bool := e.isAppOf ``Sheaf.monObj_sheafCompose_obj
    let isProof (e : Lean.Expr) : Lean.MetaM Bool := do
      let some c := e.getAppFn.constName? | return false
      unless (← Lean.getConstInfo c).type.getForallBody.isAppOf ``Precoherent do return false
      return (← Lean.Meta.inferType e).isAppOf ``Precoherent
    let proofs ← IO.mkRef (#[] : Array Lean.Expr)
    Lean.Meta.forEachExpr target fun e ↦ do
      if isInst e then
        Lean.Meta.forEachExpr e fun e' ↦ do
          if ← isProof e' then
            unless (← proofs.get).contains e' do proofs.modify (·.push e')
    let some J := target.find? fun e ↦ isInst e | throwError "no `MonObj` instance found"
    let some hStd := (J.find? (·.isAppOfArity ``coherentTopology 3)).map (·.appArg!)
      | throwError "no coherent topology found"
    let hType ← Lean.Meta.inferType hStd
    let mut goal ← goal.replaceTargetDefEq target
    let mut target := target
    for p in ← proofs.get do
      if p != hStd then
        let motive ← Lean.Meta.withLocalDeclD `h hType fun h ↦ do
          Lean.Meta.mkLambdaFVars #[h] <| target.replace fun e ↦ if isInst e then
            some (e.replace fun e' ↦ if e' == p then some h else none) else none
        let eq ← Lean.Meta.mkAppM ``Subsingleton.elim #[hStd, p]
        let propEq ← Lean.Meta.mkAppM ``congrArg #[motive, eq]
        target := motive.beta #[hStd]
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar target
        goal.assign (Lean.mkAppN (Lean.mkConst ``Eq.mp [.zero])
          #[Lean.mkApp motive hStd, Lean.mkApp motive p, propEq, next])
        goal := next.mvarId!
    Lean.Elab.Tactic.replaceMainGoal [goal]

namespace Correspondence.IsContractingAt

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {c : Correspondence ℓ K}
  {y : RationalPoint c.C} (hc : c.IsContractingAt y) (k' : Type u) [Field k'] [Algebra k k']
  {F : c.FixedLocus} {B : Over (Spec (.of k))} (j : B ⟶ F.F) {b : RationalPoint B}
  (hb : b ≫ j ≫ F.ι = y)
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k']
  [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
  [IsProper (supportClosureSpaceMap c y)]

/-- **The ambient identity `hC` of `supportCompactSupportExchange_app_lowerStar`**: an instance of
`NearbyCyclesModel.Hom.compactSupportExchange_comp_app`, once the `Precoherent Profinite` proofs
in the `MonObj` instances of `ℚ̄_ℓ` are identified. -/
theorem supportCompactSupportExchange_app_lowerStar_ambient
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    HypothesisOf (supportCompactSupportExchange_app_lowerStar hc k' j hb N) := by
  normalize_precoherent
  intro χ₀ hχ₀
  exact NearbyCyclesModel.Hom.compactSupportExchange_comp_app _ _ _ _ _ rfl rfl rfl rfl rfl rfl
    rfl rfl _ _ _ χ₀ hχ₀

/-- **The exchange `ν_c` of the support on pushforwards from a component**, without hypothesis:
`supportCompactSupportExchange_app_lowerStar` for its ambient identity
`supportCompactSupportExchange_app_lowerStar_ambient`. -/
theorem supportCompactSupportExchange_app_lowerStar_eq
    (N : Dᵇc(B.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    type_of% (supportCompactSupportExchange_app_lowerStar hc k' j hb N
      (supportCompactSupportExchange_app_lowerStar_ambient hc k' j hb N)) :=
  supportCompactSupportExchange_app_lowerStar hc k' j hb N
    (supportCompactSupportExchange_app_lowerStar_ambient hc k' j hb N)

end Correspondence.IsContractingAt

end AlgebraicGeometry.ProEtale.CondensedRing
