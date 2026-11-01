/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactificationProductExchangeDefs
import WeilConjectures.AlgebraicGeometry.SbcExchange.SbcExchangeFormal

/-! # Categorical pasting equality

A component of the compactification product-projection argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Fix the intrinsic pro-etale localization, which uses the standard derived category.
attribute [local instance 50000] proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] proEtaleRingModulePullback proEtaleConstantRingComparison
  proEtaleAmbientRingedExchange
  proEtaleRingDerivedAdjunction proEtaleRingModuleDirectImage Functor.mapDerivedCategory

private def productSquare {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) (T : Over S) :
    ChosenCartesianSquare (prod.fst : U ⨯ T ⟶ U).left
      (prod.map f (𝟙 T)).left f.left (prod.fst : V ⨯ T ⟶ V).left :=
  { toCommSq := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).toCommSq
    isoPullback := ((IsPullback.of_prod_fst_with_id f T).map (Over.forget S)).isoPullback
    hom_fst := ((IsPullback.of_prod_fst_with_id f T).map
      (Over.forget S)).isoPullback_hom_fst
    hom_snd := ((IsPullback.of_prod_fst_with_id f T).map
      (Over.forget S)).isoPullback_hom_snd }

private theorem productExchange_eq_sbc (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (T : Over S) :
    compactificationProductExchange A f T = SbcExchange.exchange A (productSquare f T) := by
  rfl

private theorem directImageComposition_eq (A : Type u) [CommRing A]
    {X B Y : Scheme.{u}} (j : X ⟶ B) (p : B ⟶ Y) :
    compactificationDirectImageComposition A j p = SbcExchange.directImageComposition A j p := by
  rfl

private theorem productComposition_eq (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X B Y : Over S} (j : X ⟶ B) (p : B ⟶ Y) (T : Over S) :
    compactificationProductDirectImageComposition A j p T =
      eqToIso (congrArg (SbcExchange.directImage A)
        (congrArg (fun q : X ⨯ T ⟶ Y ⨯ T ↦ q.left) (prod.map_comp_id j p))) ≪≫
        SbcExchange.directImageComposition A (prod.map j (𝟙 T)).left
          (prod.map p (𝟙 T)).left := by
  rfl

attribute [local irreducible] compactificationProductExchange
  compactificationDirectImageComposition compactificationProductDirectImageComposition

-- A purely categorical predicate keeps transport independent of the implementations
-- of the derived functors and comparison isomorphisms.
private def Pasting {C C' D D' E E' : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (F' : C' ⥤ D') (G' : D' ⥤ E') (H' : C' ⥤ E')
    (U : C ⥤ C') (V : D ⥤ D') (W : E ⥤ E')
    (c : H ≅ F ⋙ G) (c' : H' ≅ F' ⋙ G')
    (α : H ⋙ W ⟶ U ⋙ H') (α₁ : F ⋙ V ⟶ U ⋙ F') (α₂ : G ⋙ W ⟶ V ⋙ G') (K : C) : Prop :=
  α.app K = W.map (c.hom.app K) ≫ α₂.app (F.obj K) ≫
    G'.map (α₁.app K) ≫ c'.inv.app (U.obj K)

private theorem Pasting.congr {C C' D D' E E' : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (F' : C' ⥤ D') (G' : D' ⥤ E') (H' : C' ⥤ E')
    (U : C ⥤ C') (V : D ⥤ D') (W : E ⥤ E')
    (c : H ≅ F ⋙ G) (c' : H' ≅ F' ⋙ G')
    (α : H ⋙ W ⟶ U ⋙ H') (α₁ : F ⋙ V ⟶ U ⋙ F') (α₂ : G ⋙ W ⟶ V ⋙ G')
    (c₀ : H ≅ F ⋙ G) (c₀' : H' ≅ F' ⋙ G')
    (α₀ : H ⋙ W ⟶ U ⋙ H') (α₀₁ : F ⋙ V ⟶ U ⋙ F') (α₀₂ : G ⋙ W ⟶ V ⋙ G')
    (hc : c = c₀) (hc' : c' = c₀') (hα : α = α₀)
    (hα₁ : α₁ = α₀₁) (hα₂ : α₂ = α₀₂) (K : C)
    (h : Pasting F G H F' G' H' U V W c₀ c₀' α₀ α₀₁ α₀₂ K) :
    Pasting F G H F' G' H' U V W c c' α α₁ α₂ K := by
  subst c
  subst c'
  subst α
  subst α₁
  subst α₂
  exact h

private def pastingIdentity (A : Type u) [CommRing A]
    {X' X Y' Y Z' Z : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {g : Z' ⟶ Z}
    (sq₁ : ChosenCartesianSquare u f' f v)
    (sq₂ : ChosenCartesianSquare v e' e g)
    (b : X' ⟶ Z') (hb : b = f' ≫ e')
    (outer : ChosenCartesianSquare u b (f ≫ e) g)
    (K : proEtaleDerivedCategory X A) : Prop :=
  Pasting (SbcExchange.directImage A f) (SbcExchange.directImage A e)
    (SbcExchange.directImage A (f ≫ e)) (SbcExchange.directImage A f')
    (SbcExchange.directImage A e') (SbcExchange.directImage A b)
    (proEtaleConstantRingDerivedPullback A u) (proEtaleConstantRingDerivedPullback A v)
    (proEtaleConstantRingDerivedPullback A g)
    (SbcExchange.directImageComposition A f e)
    (eqToIso (congrArg (SbcExchange.directImage A) hb) ≪≫
      SbcExchange.directImageComposition A f' e')
    (SbcExchange.exchange A outer) (SbcExchange.exchange A sq₁)
    (SbcExchange.exchange A sq₂) K

private theorem pastingIdentity_refl (A : Type u) [CommRing A]
    {X' X Y' Y Z' Z : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {g : Z' ⟶ Z}
    (sq₁ : ChosenCartesianSquare u f' f v)
    (sq₂ : ChosenCartesianSquare v e' e g)
    (outer : ChosenCartesianSquare u (f' ≫ e') (f ≫ e) g)
    (K : proEtaleDerivedCategory X A) :
    pastingIdentity A sq₁ sq₂ (f' ≫ e') rfl outer K := by
  unfold pastingIdentity Pasting
  rw [eqToIso_refl, Iso.refl_trans]
  exact (SbcExchange.formal A).2.2.2 sq₁ sq₂ outer K

private theorem pastingTransport (A : Type u) [CommRing A]
    {X' X Y' Y Z' Z : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {g : Z' ⟶ Z}
    (sq₁ : ChosenCartesianSquare u f' f v)
    (sq₂ : ChosenCartesianSquare v e' e g)
    (b : X' ⟶ Z') (hb : b = f' ≫ e')
    (outer : ChosenCartesianSquare u b (f ≫ e) g)
    (K : proEtaleDerivedCategory X A) :
    pastingIdentity A sq₁ sq₂ b hb outer K := by
  subst b
  exact pastingIdentity_refl A sq₁ sq₂ outer K

private theorem pastingWithData_of_eq (A : Type u) [CommRing A]
    {X' X Y' Y Z' Z : Scheme.{u}} {u : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {v : Y' ⟶ Y} {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {g : Z' ⟶ Z}
    (sq₁ : ChosenCartesianSquare u f' f v)
    (sq₂ : ChosenCartesianSquare v e' e g)
    (b : X' ⟶ Z') (hb : b = f' ≫ e')
    (outer : ChosenCartesianSquare u b (f ≫ e) g)
    (c : SbcExchange.directImage A (f ≫ e) ≅
      SbcExchange.directImage A f ⋙ SbcExchange.directImage A e)
    (c' : SbcExchange.directImage A b ≅
      SbcExchange.directImage A f' ⋙ SbcExchange.directImage A e')
    (E : SbcExchange.directImage A (f ≫ e) ⋙ proEtaleConstantRingDerivedPullback A g ⟶
      proEtaleConstantRingDerivedPullback A u ⋙ SbcExchange.directImage A b)
    (E₁ : SbcExchange.directImage A f ⋙ proEtaleConstantRingDerivedPullback A v ⟶
      proEtaleConstantRingDerivedPullback A u ⋙ SbcExchange.directImage A f')
    (E₂ : SbcExchange.directImage A e ⋙ proEtaleConstantRingDerivedPullback A g ⟶
      proEtaleConstantRingDerivedPullback A v ⋙ SbcExchange.directImage A e')
    (hc : c = SbcExchange.directImageComposition A f e)
    (hc' : c' = eqToIso (congrArg (SbcExchange.directImage A) hb) ≪≫
      SbcExchange.directImageComposition A f' e')
    (hE : E = SbcExchange.exchange A outer)
    (hE₁ : E₁ = SbcExchange.exchange A sq₁)
    (hE₂ : E₂ = SbcExchange.exchange A sq₂)
    (K : proEtaleDerivedCategory X A) :
    Pasting (SbcExchange.directImage A f) (SbcExchange.directImage A e)
      (SbcExchange.directImage A (f ≫ e)) (SbcExchange.directImage A f')
      (SbcExchange.directImage A e') (SbcExchange.directImage A b)
      (proEtaleConstantRingDerivedPullback A u) (proEtaleConstantRingDerivedPullback A v)
      (proEtaleConstantRingDerivedPullback A g) c c' E E₁ E₂ K := by
  exact Pasting.congr _ _ _ _ _ _ _ _ _ c c' E E₁ E₂ _ _ _ _ _
    hc hc' hE hE₁ hE₂ K (pastingTransport A sq₁ sq₂ b hb outer K)

private theorem productPasting (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X B Y : Over S} (j : X ⟶ B) (p : B ⟶ Y) (T : Over S)
    (M : proEtaleDerivedCategory X.left A) :
    @Pasting
      (proEtaleDerivedCategory X.left A) (proEtaleDerivedCategory (X ⨯ T).left A)
      (proEtaleDerivedCategory B.left A) (proEtaleDerivedCategory (B ⨯ T).left A)
      (proEtaleDerivedCategory Y.left A) (proEtaleDerivedCategory (Y ⨯ T).left A)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A p.left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A (j ≫ p).left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A (prod.map j (𝟙 T)).left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A (prod.map p (𝟙 T)).left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A (prod.map (j ≫ p) (𝟙 T)).left).rightDerivedFunctor)
      (proEtaleConstantRingDerivedPullback A (prod.fst : X ⨯ T ⟶ X).left)
      (proEtaleConstantRingDerivedPullback A (prod.fst : B ⨯ T ⟶ B).left)
      (proEtaleConstantRingDerivedPullback A (prod.fst : Y ⨯ T ⟶ Y).left)
      (compactificationDirectImageComposition A j.left p.left)
      (compactificationProductDirectImageComposition A j p T)
      (compactificationProductExchange A (j ≫ p) T)
      (compactificationProductExchange A j T) (compactificationProductExchange A p T) M := by
  exact pastingWithData_of_eq A (productSquare j T) (productSquare p T)
    (prod.map (j ≫ p) (𝟙 T)).left
    (congrArg (fun q : X ⨯ T ⟶ Y ⨯ T ↦ q.left) (prod.map_comp_id j p))
    (productSquare (j ≫ p) T)
    (compactificationDirectImageComposition A j.left p.left)
    (compactificationProductDirectImageComposition A j p T)
    (compactificationProductExchange A (j ≫ p) T)
    (compactificationProductExchange A j T) (compactificationProductExchange A p T)
    (directImageComposition_eq A j.left p.left) (productComposition_eq A j p T)
    (productExchange_eq_sbc A (j ≫ p) T)
    (productExchange_eq_sbc A j T) (productExchange_eq_sbc A p T) M

-- The implicit presentations of the derived categories agree definitionally.
-- Decompose their field applications by heterogeneous congruence before asking
-- the kernel to compare them, keeping derived-functor data as whole arguments.
-- Every generated step is an ordinary equality proof checked by the kernel.
private theorem proofHEqOfPropEq {P Q : Prop} (e : P = Q) (hP : P) (hQ : Q) :
    HEq hP hQ := by
  subst Q
  exact proof_irrel_heq hP hQ

private meta def largeValues : List Lean.Name :=
  [``Functor.rightDerivedFunctor, ``Functor.mapDerivedCategory,
    ``proEtaleConstantRingDerivedPullback, ``compactificationProductExchange,
    ``compactificationDirectImageComposition, ``compactificationProductDirectImageComposition,
    ``SbcExchange.directImage, ``SbcExchange.exchange, ``SbcExchange.directImageComposition]

private meta def projectionAsApp (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let .proj sn i x := e.getAppFn | return e
  let ty ← Lean.Meta.whnf (← Lean.Meta.inferType x)
  let .const _ ls := ty.getAppFn | return e
  let some si := Lean.getStructureInfo? (← Lean.getEnv) sn | return e
  let ind ← Lean.getConstInfoInduct sn
  let params := ty.getAppArgs.extract 0 ind.numParams
  let f := Lean.mkAppN (Lean.mkConst si.fieldNames[i]! ls) (params.push x)
  return Lean.mkAppN f e.getAppArgs

private meta def strictHEq (a b : Lean.Expr) (fuel : Nat) : Lean.MetaM Lean.Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← Lean.Meta.mkHEqRefl a
  let a ← projectionAsApp a
  let b ← projectionAsApp b
  if a == b then return ← Lean.Meta.mkHEqRefl a
  let large (e : Lean.Expr) := (e.find? fun t ↦
    match t with
    | .const n _ => largeValues.contains n
    | _ => false).isSome
  let whole (e : Lean.Expr) :=
    e.getAppFn.isConst &&
      (largeValues.contains e.getAppFn.constName! ||
        e.getAppFn.constName! == ``Functor.comp)
  if (!large a && !large b) || (whole a && whole b) then
    unless ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq a b) do
      Lean.throwError m!"not definitionally equal: {a} / {b}"
    return ← Lean.Meta.mkHEqRefl a
  match fuel with
  | 0 => Lean.throwError m!"strict congruence depth: {a} / {b}"
  | n + 1 =>
    if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
      let pa ← Lean.Meta.inferType a
      let pb ← Lean.Meta.inferType b
      let hp ← strictHEq pa pb n
      let hp ← Lean.Meta.mkAppM ``eq_of_heq #[hp]
      return ← Lean.Meta.mkAppM ``proofHEqOfPropEq #[hp, a, b]
    let f := a.getAppFn
    let g := b.getAppFn
    let aa := a.getAppArgs
    let bb := b.getAppArgs
    if f == g && aa.size == bb.size && !aa.isEmpty then
      let thm ← Lean.Meta.mkHCongrWithArity f aa.size
      let mut args := #[]
      for x in aa, y in bb, k in thm.argKinds do
        let hp ← strictHEq x y n
        let hp ← if k == .eq then Lean.Meta.mkAppM ``eq_of_heq #[hp] else pure hp
        args := args.push x |>.push y |>.push hp
      let pr := Lean.mkAppN thm.proof args
      if (← Lean.Meta.inferType pr).isEq then
        return ← Lean.Meta.mkAppM ``heq_of_eq #[pr]
      return pr
    let a' ← Lean.Meta.unfoldDefinition? a
    let b' ← Lean.Meta.unfoldDefinition? b
    match a', b' with
    | some a', some b' => strictHEq a'.headBeta b'.headBeta n
    | some a', none => strictHEq a'.headBeta b n
    | none, some b' => strictHEq a b'.headBeta n
    | none, none => Lean.throwError m!"strict congruence stuck: {a} / {b}"

private theorem productPastingExpanded (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X B Y : Over S} (j : X ⟶ B) (p : B ⟶ Y) (T : Over S)
    (M : proEtaleDerivedCategory X.left A)
    (h : @Pasting
      (proEtaleDerivedCategory X.left A) (proEtaleDerivedCategory (X ⨯ T).left A)
      (proEtaleDerivedCategory B.left A) (proEtaleDerivedCategory (B ⨯ T).left A)
      (proEtaleDerivedCategory Y.left A) (proEtaleDerivedCategory (Y ⨯ T).left A)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A p.left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A (j ≫ p).left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A (prod.map j (𝟙 T)).left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A (prod.map p (𝟙 T)).left).rightDerivedFunctor)
      ((proEtaleConstantRingPushforward A (prod.map (j ≫ p) (𝟙 T)).left).rightDerivedFunctor)
      (proEtaleConstantRingDerivedPullback A (prod.fst : X ⨯ T ⟶ X).left)
      (proEtaleConstantRingDerivedPullback A (prod.fst : B ⨯ T ⟶ B).left)
      (proEtaleConstantRingDerivedPullback A (prod.fst : Y ⨯ T ⟶ Y).left)
      (compactificationDirectImageComposition A j.left p.left)
      (compactificationProductDirectImageComposition A j p T)
      (compactificationProductExchange A (j ≫ p) T)
      (compactificationProductExchange A j T) (compactificationProductExchange A p T) M) :
    ((compactificationProductExchange A (j ≫ p) T).app M =
      (proEtaleConstantRingDerivedPullback A (prod.fst : Y ⨯ T ⟶ Y).left).map
        ((compactificationDirectImageComposition A j.left p.left).hom.app M) ≫
      (compactificationProductExchange A p T).app
        ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor.obj M) ≫
      (proEtaleConstantRingPushforward A (prod.map p (𝟙 T)).left).rightDerivedFunctor.map
        ((compactificationProductExchange A j T).app M) ≫
      (compactificationProductDirectImageComposition A j p T).inv.app
        ((proEtaleConstantRingDerivedPullback A (prod.fst : X ⨯ T ⟶ X).left).obj M)) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let some hd := (← Lean.getLCtx).findFromUserName? `h
      | Lean.throwError "missing h"
    let h := Lean.mkFVar hd.fvarId
    let gt ← Lean.Elab.Tactic.getMainTarget
    let ht ← Lean.Meta.withTransparency .all (Lean.Meta.whnf (← Lean.Meta.inferType h))
    let hp ← strictHEq gt ht 80
    let hp ← Lean.Meta.mkAppM ``eq_of_heq #[hp]
    let pr := Lean.mkAppN (Lean.mkConst ``Eq.mpr [Lean.Level.zero]) #[gt, ht, hp, h]
    (← Lean.Elab.Tactic.getMainGoal).assign pr
    Lean.Elab.Tactic.replaceMainGoal []

private theorem productPasting_eq (A : Type u) [CommRing A]
    {S : Scheme.{u}} {X B Y : Over S} (j : X ⟶ B) (p : B ⟶ Y) (T : Over S)
    (M : proEtaleDerivedCategory X.left A) :
    ((compactificationProductExchange A (j ≫ p) T).app M =
      (proEtaleConstantRingDerivedPullback A (prod.fst : Y ⨯ T ⟶ Y).left).map
        ((compactificationDirectImageComposition A j.left p.left).hom.app M) ≫
      (compactificationProductExchange A p T).app
        ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor.obj M) ≫
      (proEtaleConstantRingPushforward A (prod.map p (𝟙 T)).left).rightDerivedFunctor.map
        ((compactificationProductExchange A j T).app M) ≫
      (compactificationProductDirectImageComposition A j p T).inv.app
        ((proEtaleConstantRingDerivedPullback A (prod.fst : X ⨯ T ⟶ X).left).obj M)) := by
  exact productPastingExpanded A j p T M (productPasting A j p T M)

set_option maxRecDepth 4000 in
-- Specialize the formal law without unfolding the ringed-site operations.
/-- Categorical pasting equality.

Source: latest blueprint det-tf-ibc-pasting.proof.md, steps 3--4; the vertical
pasting clause of `SbcExchange.formal` (det-sbc-exchange-formal).

Proof: apply vertical pasting to the canonical product squares of j and p.
The bottom arrow of the outer square is the product of j ≫ p with the identity.
Transport it by prod.map_comp_id to the composite of the two bottom arrows.
Equality elimination shows that this inserts precisely the equality isomorphism
in the product direct-image compositor. The remaining compositor is definitionally
the right-adjoint conjugate used by SbcExchange.formal. Unfold the specialization
wrappers; coefficient compatibility proofs agree by proof irrelevance. Evaluation
at M then gives the displayed equality of the actual ambient exchange arrows.

(blueprint: compactification-product-exchange-pasting-equality). -/
theorem compactificationProductExchange_pasting_equality
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k) (A : Type u) [CommRing A] [Finite A]
    (_hA : ∃ r : ℕ, 0 < r ∧ ((l ^ r : ℕ) : A) = 0)
    (X Y T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (B : Over (Spec (.of D.k))) (j : X ⟶ B) [IsOpenImmersion j.left]
    (p : B ⟶ Y) [IsProper p.left] (M : proEtaleDerivedCategory X.left A)
    (_hM : (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} A) X.left) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X.left A).essImage M) :
    ((compactificationProductExchange A (j ≫ p) T).app M =
      (proEtaleConstantRingDerivedPullback A (prod.fst : Y ⨯ T ⟶ Y).left).map
        ((compactificationDirectImageComposition A j.left p.left).hom.app M) ≫
      (compactificationProductExchange A p T).app
        ((proEtaleConstantRingPushforward A j.left).rightDerivedFunctor.obj M) ≫
      (proEtaleConstantRingPushforward A (prod.map p (𝟙 T)).left).rightDerivedFunctor.map
        ((compactificationProductExchange A j T).app M) ≫
      (compactificationProductDirectImageComposition A j p T).inv.app
        ((proEtaleConstantRingDerivedPullback A (prod.fst : X ⨯ T ⟶ X).left).obj M))  := by
  exact productPasting_eq A j p T M

end AlgebraicGeometry.Scheme
