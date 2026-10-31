/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompositionEquation
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierIntegralCompNormalization
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition

/-! Tower component of normalized finite Verdier coherence.

Source: thm-coef-qbar-verdier, composition clause.
(blueprint: lem-coef-qbar-verdier-finite-tower-equation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage transition associator)
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem normalized_scalar_tower
    (A : Type u) [Field A] [Algebra (Padic l) A] [FiniteDimensional (Padic l) A]
    (B : Type u) [Field B] [Algebra (Padic l) B] [FiniteDimensional (Padic l) B]
    (C : Type u) [Field C] [Algebra (Padic l) C] [FiniteDimensional (Padic l) C]
    (i : A →ₐ[Padic l] B) (j : B →ₐ[Padic l] C) (q : A →ₐ[Padic l] C)
    (hq : j.comp i = q)
    (wA : IntegralFiniteExtension.DualizingDatum l X D hl A)
    (wB : IntegralFiniteExtension.DualizingDatum l X D hl B)
    (wC : IntegralFiniteExtension.DualizingDatum l X D hl C)
    (a : RationalVerdier.Datum D l hl X A wA)
    (b : RationalVerdier.Datum D l hl X B wB)
    (c : RationalVerdier.Datum D l hl X C wC)
    (eAB : RationalVerdier.Extension D l hl X A B i wA wB a b)
    (eBC : RationalVerdier.Extension D l hl X B C j wB wC b c)
    (eAC : RationalVerdier.Extension D l hl X A C q wA wC a c)
    (hAB : RationalVerdier.ExtensionProperties D l hl X A B i wA wB a b eAB)
    (hBC : RationalVerdier.ExtensionProperties D l hl X B C j wB wC b c eBC)
    (hAC : RationalVerdier.ExtensionProperties D l hl X A C q wA wC a c eAC)
    (K : sfRationalConstructibleCategory l A X) :
    (RationalVerdier.scalar l X B C j).map (eAB.comparison.hom.app (op K)) ≫
        eBC.comparison.hom.app (op ((RationalVerdier.scalar l X A B i).obj K)) =
      (GeneralAlgebraicallyClosedCoefficients.scalarAssociator l A B C i j q hq X).hom.app
          (a.dual.obj (op K)) ≫
        eAC.comparison.hom.app (op K) ≫ c.dual.map
          ((GeneralAlgebraicallyClosedCoefficients.scalarAssociator l A B C i j q hq X).hom.app
            K).op := by
  subst q
  let t := sfRationalScalarComp l A B i X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) C j
  have hn (T : sfIntegralConstructibleCategory l A X) :
      HEq (t.hom.app ((sfRationalConstructibleLocalization l A X).obj T))
        ((sfRationalConstructibleLocalization l C X).map
          (ObjectProperty.homMk
            (X := (RationalVerdier.integralScalar l X B C j).obj
              ((RationalVerdier.integralScalar l X A B i).obj T))
            (Y := (RationalVerdier.integralScalar l X A C (j.comp i)).obj T)
            (IntegralFiniteExtension.comp l A B i X C j T.obj T.property.1).hom)) := by
    have hn := (sfRationalScalarComp_existsUnique l A B i X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) C j).exists.choose_spec
      ((sfRationalConstructibleLocalization l A X).obj T)
    dsimp only [sfRationalConstructibleLocalization, ScalarLocalization.localization,
      Functor.obj] at hn
    rw [RationalVerdier.integral_comp_normalization_bridge (l := l) (X := X)
      A B C i j T] at hn
    exact hn
  have he := RationalVerdier.extension_composition_equation D l hl X
    A B C i j wA wB wC a b c t hn eAB eBC eAC hAB hBC hAC K
  simpa only [GeneralAlgebraicallyClosedCoefficients.scalarAssociator, Iso.trans_hom,
    NatTrans.comp_app, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
    using he

attribute [local irreducible] sfRationalScalarExtension
  sfConstructibleIntegralScalarExtension
  GeneralAlgebraicallyClosedCoefficients.scalarAssociator
  GeneralAlgebraicallyClosedCoefficients.associator
  AlgebraicallyClosedCoefficients.coefficientInclusion

attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

/- Construct an ordinary HEq proof by congruence, reducing only the category aliases
   and the functor projections. This avoids unfolding completed scalar extensions. -/
private meta def towerDefeq (fuel : Nat) (a b : Lean.Expr) : Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => throwError "congruence depth"
  | fuel + 1 =>
    if a == b then return ← Lean.Meta.mkHEqRefl a
    let a' ← if a.isAppOf ``Functor.obj || a.isAppOf ``Functor.map ||
        a.isAppOf ``Opposite.unop then
      Lean.Meta.withTransparency .default (Lean.Meta.whnf a)
      else pure a
    let b' ← if b.isAppOf ``Functor.obj || b.isAppOf ``Functor.map ||
        b.isAppOf ``Opposite.unop then
      Lean.Meta.withTransparency .default (Lean.Meta.whnf b)
      else pure b
    if a != a' || b != b' then return ← towerDefeq fuel a' b'
    if a.isApp && b.isApp && a.getAppFn == b.getAppFn &&
        a.getAppNumArgs == b.getAppNumArgs then
      let thm ← Lean.Meta.mkHCongrWithArity a.getAppFn a.getAppNumArgs
      let mut args := #[]
      for x in a.getAppArgs, y in b.getAppArgs, kind in thm.argKinds do
        match kind with
        | .eq =>
          let h ← towerDefeq fuel x y
          let h ← Lean.Meta.mkAppM ``eq_of_heq #[h]
          args := args ++ #[x,y,h]
        | .heq => args := args ++ #[x,y, ← towerDefeq fuel x y]
        | _ => throwError "unexpected congr kind"
      let h := Lean.mkAppN thm.proof args
      let ht ← Lean.Meta.inferType h
      if ht.isEq then return ← Lean.Meta.mkAppM ``heq_of_eq #[h]
      return h
    if a.isLambda && b.isLambda then
      return ← Lean.Meta.withLocalDeclD `x a.bindingDomain! fun x => do
        let h ← towerDefeq fuel (a.bindingBody!.instantiate1 x) (b.bindingBody!.instantiate1 x)
        let h ← Lean.Meta.mkAppM ``eq_of_heq #[h]
        let h ← Lean.Meta.mkLambdaFVars #[x] h
        return ← Lean.Meta.mkAppM ``heq_of_eq #[← Lean.Meta.mkAppM ``funext #[h]]
    let A ← Lean.Meta.inferType a
    let B ← Lean.Meta.inferType b
    if (← Lean.Meta.isProp A) && (← Lean.Meta.isDefEq A B) then
      return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
    let a' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf a)
    let b' ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf b)
    if a' != a || b' != b then return ← towerDefeq fuel a' b'
    unless ← Lean.Meta.isDefEq a b do
      throwError "different: {a} AND {b}"
    return ← Lean.Meta.mkHEqRefl a

/-- The tower component equation for a finite Verdier datum.
Source: thm-coef-qbar-verdier, final coefficient-transport paragraph;
(blueprint: lem-coef-qbar-verdier-finite-tower-equation).

Proof: identify the three coefficient inclusions and their composite using the
coefficient-inclusion composition law. Apply RationalVerdier.extension_composition
to the normalized extensions and use its integral normalization clause. The canonical
scalar associator has the same normalized integral component, by its uniqueness
specification. Transport the resulting equality through the stage associator and
retain the dependent endpoint equality as HEq. Repeated fields, zero objects, and the
empty scheme are included automatically. -/
theorem finite_tower_equation (F : Finite D l hl Ω X) :
    ∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) (K : Stage l Ω X E),
    HEq
      ((transition l Ω X L M k).map ((F.beta E L h).hom.app (op K)) ≫
        (F.beta L M k).hom.app (op ((transition l Ω X E L h).obj K)))
      ((associator l Ω X E L M h k).hom.app ((F.datum E).dual.obj (op K)) ≫
        (F.beta E M (h.trans k)).hom.app (op K) ≫
          (F.datum M).dual.map ((associator l Ω X E L M h k).hom.app K).op) := by
  intro E L M h k K
  have hbEL := eq_of_heq (F.betaNormalized E L h)
  have hbLM := eq_of_heq (F.betaNormalized L M k)
  have hbEM := eq_of_heq (F.betaNormalized E M (h.trans k))
  have ha : associator l Ω X E L M h k =
      GeneralAlgebraicallyClosedCoefficients.scalarAssociator l
        (Coefficient l Ω E) (Coefficient l Ω L) (Coefficient l Ω M)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω L M k)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E M (h.trans k))
        ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k) X := by
    unfold GeneralAlgebraicallyClosedCoefficients.associator
    exact eq_of_heq
      ((GeneralAlgebraicallyClosedCoefficients.associator_existsUnique
        l Ω X E L M h k).exists.choose_spec)
  have he := normalized_scalar_tower D l hl X
    (Coefficient l Ω E) (Coefficient l Ω L) (Coefficient l Ω M)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω L M k)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E M (h.trans k))
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k)
    (F.omega E) (F.omega L) (F.omega M) (F.datum E) (F.datum L) (F.datum M)
    (F.scalar E L h) (F.scalar L M k) (F.scalar E M (h.trans k))
    (F.normalized E L h) (F.normalized L M k) (F.normalized E M (h.trans k)) K
  simp -implicitDefEqProofs only [hbEL, hbLM, hbEM, ha]
  apply heq_of_eq
  dsimp only [transition, RationalVerdier.scalar, Functor.comp_obj, Functor.op_obj,
    unop_op, GeneralAlgebraicallyClosedCoefficients.Stage,
    GeneralAlgebraicallyClosedCoefficients.stageCategory] at he ⊢
  -- The stage and rational presentations differ only by aliases and proof arguments.
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
    let G ← Lean.instantiateMVars (← g.getType)
    let hd ← Lean.Meta.getLocalDeclFromUserName `he
    let H ← Lean.instantiateMVars hd.type
    let e ← towerDefeq 100 H G
    let e ← Lean.Meta.mkAppM ``eq_of_heq #[e]
    let p := Lean.mkAppN (.const ``Eq.mp [0]) #[H,G,e,hd.toExpr]
    g.assign p

end WeilConjectures.CoefQbarVerdier
