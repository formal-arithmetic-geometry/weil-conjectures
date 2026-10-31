/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGluing
public import WeilConjectures.AlgebraicGeometry.FiniteAdjointCompositorTransposes
import WeilConjectures.AlgebraicGeometry.FiniteNormalizedCompositorFixedCoordinates

/-! # Finite normalization of the given tower left compositor

This is the finite evaluation step of the actual tower compositor argument.
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

-- The term-congruence transport follows the proved private helper in
-- WeilConjectures.AlgebraicGeometry.ExceptionalSupportProjectionIso. It keeps proof-irrelevant instance
-- changes outside the large derived-functor implementations.
section InstanceTransport
open Lean Meta Elab Tactic CategoryTheory

private theorem instanceProofsHEq {P Q : Prop} (p : P) (q : Q) : HEq p q := by
  have h : P = Q := propext ⟨fun _ ↦ q, fun _ ↦ p⟩
  cases h
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
          h.isConstOf ``ObjectProperty.lift || h.isConstOf ``SpTowerCalculus.inclusion ||
          h.isConstOf ``SpTowerCalculus.fixedLevel || h.isConstOf ``finiteAdjointSupport ||
          h.isConstOf ``reductionCtfCompactSupport then
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
      if ← isProp (← inferType a) then
        return ← mkAppM ``instanceProofsHEq #[a, b]
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
      let sharedType := af.isConstOf ``DerivedCategory ||
        af.isConstOf ``instCategoryDerivedCategory || af.isConstOf ``Sheaf ||
        af.isConstOf ``ObjectProperty.FullSubcategory.category ||
        af.isConstOf ``Functor.category || af.isConstOf ``CategoryTheory.Functor ||
        af.isConstOf ``HasDerivedCategory.ofIsGrothendieckAbelian
      if sharedType then
        if ← withReducible (isDefEq a b) then return ← mkHEqRefl a
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
      if af.isConstOf ``finiteAdjointSupport ||
          af.isConstOf ``reductionCtfCompactSupport then
        if let some a' ← withDefault <| unfoldDefinition? a then
          return ← instanceCongr cache norm fuel a' b
      if bf.isConstOf ``finiteAdjointSupport ||
          bf.isConstOf ``reductionCtfCompactSupport then
        if let some b' ← withDefault <| unfoldDefinition? b then
          return ← instanceCongr cache norm fuel a b'
      if af != bf then
        if af.isConstOf ``AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory ||
            af.isConstOf ``AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory then
          if let some a' ← withDefault <| unfoldDefinition? a then
            return ← instanceCongr cache norm fuel a' b
        if bf.isConstOf ``AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory ||
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
    let q ← instanceCongr cache (userName == `hfinite) 500 target (← instantiateMVars d.type)
    let e ← mkAppM ``eq_of_heq #[q]
    let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
    (← getMainGoal).assign pf
end InstanceTransport

end AlgebraicGeometry.ProEtale

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  AlgebraicGeometry.ProEtale.SpTowerCalculus.finiteCanonicalComposition

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

private theorem coordinate_compositor_paste
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {QY : C ⥤ C'} {QZ : D ⥤ D'} [QZ.Faithful]
    {G : C ⥤ D} {G' : C' ⥤ D'}
    (s : NatTrans (G ⋙ QZ) (QY ⋙ G'))
    {U V H : D} {N L : C} {L' : C'} {H' : D'}
    (sh : QZ.obj H ⟶ H') [Mono sh]
    {a : U ⟶ V} {bh : V ⟶ H} {bg : U ⟶ G.obj N}
    {bf : N ⟶ L} {ac : G.obj L ⟶ H}
    (sf : QY.obj L ⟶ L') (ahat : G'.obj L' ⟶ H')
    (hcoh : QZ.map a ≫ QZ.map bh ≫ sh =
      QZ.map bg ≫ s.app N ≫ G'.map (QY.map bf) ≫ G'.map sf ≫ ahat)
    (hfinite : QZ.map ac ≫ sh = s.app L ≫ G'.map sf ≫ ahat) :
    a ≫ bh = bg ≫ G.map bf ≫ ac := by
  apply QZ.map_injective
  apply (cancel_mono sh).1
  simp only [Functor.map_comp, Category.assoc]
  have hn := s.naturality bf
  change QZ.map (G.map bf) ≫ s.app L =
    s.app N ≫ G'.map (QY.map bf) at hn
  rw [hcoh, ← reassoc_of% hn, ← hfinite]

private theorem coordinate_compositor_functors
    {Tx Ty Tz Cx Cy Cz Cx' Cy' Cz' : Type*}
    [Category* Tx] [Category* Ty] [Category* Tz]
    [Category* Cx] [Category* Cy] [Category* Cz]
    [Category* Cx'] [Category* Cy'] [Category* Cz']
    {P : ObjectProperty Tx}
    {TF : Tx ⥤ Ty} {TG : Ty ⥤ Tz} {TH : Tx ⥤ Tz}
    {EX : Tx ⥤ Cx} {EY : Ty ⥤ Cy} {EZ : Tz ⥤ Cz}
    {QX : Cx ⥤ Cx'} {QY : Cy ⥤ Cy'} {QZ : Cz ⥤ Cz'} [QZ.Faithful]
    {Ff : Cx ⥤ Cy} {Fg : Cy ⥤ Cz} {Fh : Cx ⥤ Cz}
    {J : Cx' ⥤ Cy'} {G : Cy' ⥤ Cz'} {B : Cx' ⥤ Cz'}
    (a : NatTrans (P.ι ⋙ TF ⋙ TG) (P.ι ⋙ TH))
    (vf₀ vf : NatTrans (TF ⋙ EY) (EX ⋙ Ff))
    (vg₀ vg : NatTrans (TG ⋙ EZ) (EY ⋙ Fg))
    (vh₀ vh : NatTrans (TH ⋙ EZ) (EX ⋙ Fh))
    (sf sf₀ : NatTrans (Ff ⋙ QY) (QX ⋙ J))
    (sg sg₀ : NatTrans (Fg ⋙ QZ) (QY ⋙ G))
    (sh sh₀ : NatTrans (Fh ⋙ QZ) (QX ⋙ B))
    (hsf : sf₀ = sf) (hsg : sg₀ = sg) (hsh : sh₀ = sh)
    (hshIso : ∀ L : Cx, IsIso (sh.app L))
    (bf : NatTrans (TF ⋙ EY ⋙ QY) (EX ⋙ QX ⋙ J))
    (bg : NatTrans (TG ⋙ EZ ⋙ QZ) (EY ⋙ QY ⋙ G))
    (bh : NatTrans (TH ⋙ EZ ⋙ QZ) (EX ⋙ QX ⋙ B))
    {O : ObjectProperty Cx'} (alpha : NatTrans (O.ι ⋙ J ⋙ G) (O.ι ⋙ B))
    (M : P.FullSubcategory)
    {ac : Fg.obj (Ff.obj (EX.obj M.obj)) ⟶ Fh.obj (EX.obj M.obj)}
    (h₁ : O ((EX ⋙ QX).obj M.obj)) (h₂ : O (QX.obj (EX.obj M.obj)))
    (ef : bf.app M.obj = QY.map (vf₀.app M.obj) ≫ sf.app (EX.obj M.obj))
    (eg : bg.app (TF.obj M.obj) =
      QZ.map (vg₀.app (TF.obj M.obj)) ≫ sg.app (EY.obj (TF.obj M.obj)))
    (eh : bh.app M.obj = QZ.map (vh₀.app M.obj) ≫ sh.app (EX.obj M.obj))
    (nf : vf₀.app M.obj = vf.app M.obj)
    (ng : vg₀.app (TF.obj M.obj) = vg.app (TF.obj M.obj))
    (nh : vh₀.app M.obj = vh.app M.obj)
    (hcoh : (EZ ⋙ QZ).map (a.app M) ≫ bh.app M.obj =
      bg.app (TF.obj M.obj) ≫ G.map (bf.app M.obj) ≫
        alpha.app ⟨(EX ⋙ QX).obj M.obj, h₁⟩)
    (hfinite : QZ.map ac ≫ sh₀.app (EX.obj M.obj) =
      sg₀.app (Ff.obj (EX.obj M.obj)) ≫ G.map (sf₀.app (EX.obj M.obj)) ≫
        alpha.app ⟨QX.obj (EX.obj M.obj), h₂⟩) :
    EZ.map (a.app M) ≫ vh.app M.obj =
      vg.app (TF.obj M.obj) ≫ Fg.map (vf.app M.obj) ≫ ac := by
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  cases hh
  subst sf₀
  subst sg₀
  subst sh₀
  simp only [ef, eg, eh, nf, ng, nh, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc] at hcoh
  let := hshIso (EX.obj M.obj)
  exact coordinate_compositor_paste sg (sh.app (EX.obj M.obj))
    (sf.app (EX.obj M.obj)) (alpha.app ⟨QX.obj (EX.obj M.obj), h₁⟩) hcoh hfinite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [QuasiCompact f] [QuasiCompact g]
  {cf : Compactification f} {cg : Compactification g} {ch : Compactification (f ≫ g)}

set_option maxHeartbeats 200000 in
-- Expanding the evaluation word checks several nested derived functor associators.
private theorem fixed_evaluation_hom_app
    (z : SpTowerCalculus.FiniteCoordinates l E)
    {T U : Scheme.{u}} {h : T ⟶ U} (c : Compactification h) (n : ℕ)
    (v : SpTowerCalculus.Evaluation l E b o q c n)
    (K : spDerivedCoefficientTowers l E T (q.abelian T)) :
    (SpTowerCalculus.fixedEvaluation l E b o q z c n v).hom.app K =
      (sfIntrinsicDerivedEquivalence U (SpTowerShriek.R l E n)).inverse.map
          (v.comparison.hom.app K) ≫
        (SpTowerCalculus.fixedSupportCoordinates l E b z c n).hom.app
          ((spDerivedCoefficientEvaluation l E T (q.abelian T) n).obj K) := by
  simp only [SpTowerCalculus.fixedEvaluation, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]

private theorem support_coordinates_eq
    (z : SpTowerCalculus.FiniteCoordinates l E) (n : ℕ)
    {T U : Scheme.{u}} {h : T ⟶ U} (c : Compactification h) :
    (SpTowerCalculus.fixedSupportCoordinatesFinite l E z c n).hom =
      (SpTowerCalculus.fixedSupportCoordinates l E b z c n).hom := rfl

set_option maxHeartbeats 200000 in
-- The comparison transports several nested derived-category instance arguments.
/-- The supplied proper/open tower compositor evaluates to any finite compositor
with the specified etale counit normalization. Only the left comparison is asserted.
Source: blueprint, smooth-purity composition comparisons proof (3), and the parent
node lem-sp-tower-adjoint-compositor-realization, steps 2--3
(blueprint: lem-sp-tower-compositor-finite-evaluation).

Proof: The coherence.composition_finite field of cal gives the evaluation formula
in fixed module coordinates, using cal.finite.evaluation. Each Evaluation has the
same comparison: its normalization field writes that comparison as the same word
of the realization counits and Fcomparison. Thus replace all three evaluations by
vf, vg, vh. At level n, cal.finite.finite_origin realizes the evaluated input by a
bounded constructible etale complex. The normalization of (A n).alpha identifies
its value on that witness with the etale proper/open compositor transported through
finiteAdjointSiteSupportIso. Finite compact-site coherence identifies this with
finiteCanonicalComposition in the fixed-coordinate formula. Naturality transports
that equality along the witness isomorphism. Finally the intrinsic/fixed derived
comparison is fully faithful, so cancel it to obtain the displayed equality. This
uses faithfulness of the site equivalence at one finite level, never faithfulness
of evaluation out of the derived tower category. -/
theorem towerCompositorFiniteEvaluation
    (p : ℕ) [Fact p.Prime] (_hpl : p ≠ l) (k : Type u) [Field k] [CharP k p]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (z : SpTowerCalculus.FiniteCoordinates l E)
    (hP : SpTowerCalculus.Preservation l E k b o q)
    (cal : SpTowerCalculus.Calculus l E k b o q z hP)
    (vf : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q cf n)
    (vg : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q cg n)
    (vh : ∀ n : ℕ, SpTowerCalculus.Evaluation l E b o q ch n)
    (A : ∀ n : ℕ, FiniteAdjointCompositorDatum (SpTowerShriek.R l E n) cf cg ch)
    (n : ℕ) (M : SpTowerCalculus.C l E b q X) :
    (spDerivedCoefficientEvaluation l E Z (q.abelian Z) n).map
        ((cal.composition.composition f g (f ≫ g) rfl cf cg ch).hom.app M) ≫
      (vh n).comparison.hom.app M.obj =
    (vg n).comparison.hom.app ((SpTowerCalculus.F l E b o q cf).obj M.obj) ≫
      (reductionCompactSupport (SpTowerShriek.R l E n) cg.i cg.g).map
        ((vf n).comparison.hom.app M.obj) ≫
      ((A n).alpha.hom.app ((SpTowerGluing.level l E b q X n).obj M)).hom := by
  have hcoh := cal.coherence.composition_finite f g cf cg ch M n
  obtain ⟨L, hL, ⟨w⟩⟩ := cal.finite.finite_origin M n
  let K : spFiniteConstructibleTorCategory X (SpTowerShriek.R l E n) :=
    ⟨(spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj M.obj,
      M.property.1 n⟩
  change _ = _ ≫ _ ≫ ((A n).alpha.hom.app K).hom
  let Le : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))) := ⟨L, hL⟩
  have hfinite := finiteNormalizedCompositorFixedCoordinates l p _hpl k E n z f g
    cf cg ch (A n) K Le w
  refine coordinate_compositor_functors
    (TF := SpTowerCalculus.F l E b o q cf)
    (TG := SpTowerCalculus.F l E b o q cg)
    (TH := SpTowerCalculus.F l E b o q ch)
    (EX := spDerivedCoefficientEvaluation l E X (q.abelian X) n)
    (EY := spDerivedCoefficientEvaluation l E Y (q.abelian Y) n)
    (EZ := spDerivedCoefficientEvaluation l E Z (q.abelian Z) n)
    (QX := (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse)
    (QY := (sfIntrinsicDerivedEquivalence Y (SpTowerShriek.R l E n)).inverse)
    (QZ := (sfIntrinsicDerivedEquivalence Z (SpTowerShriek.R l E n)).inverse)
    (cal.composition.composition f g (f ≫ g) rfl cf cg ch).hom
    (cal.finite.evaluation cf n).comparison.hom (vf n).comparison.hom
    (cal.finite.evaluation cg n).comparison.hom (vg n).comparison.hom
    (cal.finite.evaluation ch n).comparison.hom (vh n).comparison.hom
    (SpTowerCalculus.fixedSupportCoordinates l E b z cf n).hom
    (SpTowerCalculus.fixedSupportCoordinatesFinite l E z cf n).hom
    (SpTowerCalculus.fixedSupportCoordinates l E b z cg n).hom
    (SpTowerCalculus.fixedSupportCoordinatesFinite l E z cg n).hom
    (SpTowerCalculus.fixedSupportCoordinates l E b z ch n).hom
    (SpTowerCalculus.fixedSupportCoordinatesFinite l E z ch n).hom
    (support_coordinates_eq l E b z n cf)
    (support_coordinates_eq l E b z n cg)
    (support_coordinates_eq l E b z n ch)
    (fun L => by infer_instance)
    (SpTowerCalculus.fixedEvaluation l E b o q z cf n (cal.finite.evaluation cf n)).hom
    (SpTowerCalculus.fixedEvaluation l E b o q z cg n (cal.finite.evaluation cg n)).hom
    (SpTowerCalculus.fixedEvaluation l E b o q z ch n (cal.finite.evaluation ch n)).hom
    (SpTowerCalculus.finiteCanonicalComposition
      (ULift.{u + 1} (SpTowerShriek.R l E n)) f g cf cg ch).hom
    (ac := ((A n).alpha.hom.app K).hom) M
    (cal.finite.finite_origin M n) ⟨Le.obj, Le.property, ⟨w⟩⟩
    (fixed_evaluation_hom_app l E b o q z cf n (cal.finite.evaluation cf n) M.obj)
    (fixed_evaluation_hom_app l E b o q z cg n (cal.finite.evaluation cg n)
      ((SpTowerCalculus.F l E b o q cf).obj M.obj))
    (fixed_evaluation_hom_app l E b o q z ch n (cal.finite.evaluation ch n) M.obj)
    (((cal.finite.evaluation cf n).normalization M.obj).trans
      ((vf n).normalization M.obj).symm)
    (((cal.finite.evaluation cg n).normalization
      ((SpTowerCalculus.F l E b o q cf).obj M.obj)).trans
      ((vg n).normalization ((SpTowerCalculus.F l E b o q cf).obj M.obj)).symm)
    (((cal.finite.evaluation ch n).normalization M.obj).trans
      ((vh n).normalization M.obj).symm)
    ?_ ?_
  · as_aux_lemma => run_tac transportInstances `hcoh
  -- Keep this transport in the ambient context: closure abstraction would compare
  -- the finite component's full-subcategory types after losing the shared local input.
  · run_tac transportInstances `hfinite

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
