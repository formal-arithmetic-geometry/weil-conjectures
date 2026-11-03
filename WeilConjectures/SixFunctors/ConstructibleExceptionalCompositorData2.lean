/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Compact.CompactSupportTermHomFinite
import WeilConjectures.Mathlib.CategoryTheory.CofilteredSystem

/-! # Canonical constructible exceptional composition

Source: blueprint main-20261015, Verdier exchange, proof Step 1
(blueprint: def-sf-constructible-exceptional-compositor-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

attribute [local irreducible] sfCompactSupportTransition
  sfIntegralCompactSupportValue in
set_option backward.isDefEq.respectTransparency true in
private theorem finiteIntegralFunctor_projections
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    (hF : SfCompactSupportFiniteRealizationSpec_legacy l K₀ hl c E F) :
    letI := integralOperationsDerivedCountableProducts l E Y
    ∃ q : ∀ n : ℕ,
      F ⋙
          (sfIntegralConstructible l E Y).ι ⟶
        (sfIntegralConstructible l E X).ι ⋙
          compactSupportRestrictedLevel l E c n,
      ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
        HEq ((q n).app K)
          (Classical.choose (Classical.choose_spec (exists_isDerivedLimit_and_iso
            (sfCompactSupportTerm l E c K.obj)
            (sfCompactSupportTransition l E c K.obj)).1) ≫
              CategoryTheory.Limits.Pi.π (sfCompactSupportTerm l E c K.obj) n) := by
  letI := integralOperationsDerivedCountableProducts l E Y
  obtain ⟨_, _, _, ⟨delta, hdelta⟩, _⟩ := hF
  -- Extract the recorded functors without re-elaborating their nested choice terms.
  -- The generated term is an application of the proved generic projection lemma.
  run_tac Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.getLCtx
    let some gd := ctx.findFromUserName? `delta | throwError "missing comparison"
    let some hd := ctx.findFromUserName? `hdelta | throwError "missing normalization"
    let gamma := gd.toExpr
    let hgamma := hd.toExpr
    Lean.Meta.forallTelescopeReducing (← Lean.Meta.inferType hgamma) fun vars raw ↦ do
      let body := raw.consumeMData
      let args := body.getAppArgs
      unless args.size == 4 do
        throwError "expected HEq with four arguments, got {body.getAppFn}, {args.size}"
      let p ← Lean.Meta.mkLambdaFVars vars args[3]!
      let rhsType := args[2]!.getAppArgs
      let v ← Lean.Meta.mkLambdaFVars #[vars[0]!] rhsType[rhsType.size - 2]!
      let gt := (← Lean.Meta.inferType gamma).getAppArgs
      let f := gt[gt.size - 2]!
      let target := gt[gt.size - 1]!.getAppArgs
      let i := target[target.size - 2]!
      let composite := target[target.size - 1]!.getAppArgs
      let tower := composite[composite.size - 2]!
      let limit := composite[composite.size - 1]!
      let lhs := args[1]!.consumeMData
      let outer := lhs.getAppArgs
      unless outer.size ≥ 2 do
        throwError "expected composite, got {lhs.getAppFn}, {outer.size}"
      let rest := outer[outer.size - 1]!.consumeMData
      let inner := rest.getAppArgs
      unless inner.size ≥ 2 do
        throwError "expected second composite, got {rest.getAppFn}, {inner.size}"
      let b := inner[inner.size - 2]!.consumeMData
      let c := inner[inner.size - 1]!.consumeMData
      unless b.getAppArgs.size ≥ 2 && c.getAppArgs.size ≥ 2 do
        throwError "expected components, got {b.getAppFn}, {c.getAppFn}"
      let bn := b.getAppArgs[b.getAppArgs.size - 2]!.consumeMData
      let cn := c.getAppArgs[c.getAppArgs.size - 2]!.consumeMData
      unless cn.getAppArgs.size > 0 do
        throwError "expected evaluation hom, got {cn.getAppFn}"
      let e := cn.getAppArgs[cn.getAppArgs.size - 1]!.appFn!
      let pi := bn.appFn!
      let et := (← Lean.Meta.inferType cn.getAppArgs[cn.getAppArgs.size - 1]!).getAppArgs
      let left := et[et.size - 2]!.getAppArgs
      let eval := left[left.size - 1]!.appFn!
      let levels := et[et.size - 1]!.appFn!
      let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo
        (Lean.mkIdent `projections_from_realization)
      let it := (← Lean.Meta.inferType i).getAppArgs
      let tt := (← Lean.Meta.inferType tower).getAppArgs
      let lt := (← Lean.Meta.inferType limit).getAppArgs
      let proof ← Lean.Meta.withTransparency .all <| Lean.Meta.mkAppOptM name
        #[some it[0]!, some it[2]!, some tt[2]!, some lt[2]!,
        some it[1]!, some it[3]!, some tt[3]!, some lt[3]!,
        some i, some f, some tower, some limit,
        some eval, some levels, some e, some pi, some v, some p,
        some gamma, some hgamma]
      (← Lean.Elab.Tactic.getMainGoal).assign proof
      Lean.Elab.Tactic.replaceMainGoal []

/-- The operation datum's integral support is the specified normalized realization.
Source: blueprint exceptional adjunction, integral construction, and the operation
normalizations (blueprint: def-sf-constructible-exceptional-compositor-data).

Proof:
1. Project supportConstruction from S.higher and the realization specification of
   sfCompactSupportFiniteIntegralFunctor. Their object-normalization clauses give
   the same sfIntegralCompactSupportValue, so first transport to these fixed objects.
2. For a morphism v, naturality of the two strict-tower comparisons and their
   projection normalizations identify the composites of both image maps with every
   fixed Roos projection. The finite maps are the same proper/open reduction maps.
3. To deduce equality of the image maps, apply the Milnor exact sequence for maps
   into the total derived inverse limit. Its kernel is lim^1 of the degree-minus-one
   Hom tower. Reduction adjunction identifies these Hom groups with finite-level
   constructible Ext groups. They are finite by constructible etale finiteness over
   the algebraically closed finite-field base, using etale origin and the common
   bounded constructible intervals. An inverse sequence of finite groups is
   Mittag-Leffler: in each finite target its descending images stabilize. Hence this
   lim^1 vanishes. Equality of the fixed projection composites now implies equality
   of maps into this total limit. This uses finiteness, not faithfulness of finite
   evaluation on arbitrary derived systems.
4. The full-subcategory inclusion is faithful. Apply functor extensionality to the
   object equalities and transported map equalities; proof irrelevance identifies
   the constructibility witnesses. This proves equality of the normalized functors,
   so eqToIso below is the identity transport of their common normalization. -/
theorem constructibleIntegralSupport_eq
    (D : FiniteFieldDatum.{u}) (B : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic B.l) E]
    [FiniteDimensional (Padic B.l) E] (n : ℕ+) (S : SixFunctorOperationDatum D B E n n.pos)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) :
    S.higher.integral.support f c =
      sfCompactSupportFiniteIntegralFunctor B.l D.k
        (PurCompactSupport.coefficientPrimeUnit B.l D B.different) c E := by
  letI := integralOperationsDerivedCountableProducts B.l E Y.obj.left
  let hl := PurCompactSupport.coefficientPrimeUnit B.l D B.different
  let iX := (sfIntegralConstructible B.l E X.obj.left).ι
  let iY := (sfIntegralConstructible B.l E Y.obj.left).ι
  let F := S.higher.integral.support f c
  let G := sfCompactSupportFiniteIntegralFunctor B.l D.k hl c E
  let V := sfIntegralCompactSupportValue B.l E D.k hl c
  let L (n : ℕ) := iX ⋙ compactSupportRestrictedLevel B.l E c n
  let p (K : sfIntegralConstructibleCategory B.l E X.obj.left) (n : ℕ) :=
    Classical.choose (Classical.choose_spec (exists_isDerivedLimit_and_iso
      (sfCompactSupportTerm B.l E c K.obj)
      (sfCompactSupportTransition B.l E c K.obj)).1) ≫
        CategoryTheory.Limits.Pi.π (sfCompactSupportTerm B.l E c K.obj) n
  obtain ⟨T, _, _, hF, gamma, hgamma, _⟩ := S.higher.supportConstruction f hl c
  let qF (n : ℕ) : F ⋙ iY ⟶ L n :=
    gamma.hom ≫ Functor.whiskerLeft iX
      (Functor.whiskerLeft T.tower (T.projections n) ≫ (T.evaluations n).hom)
  have hG : SfCompactSupportFiniteRealizationSpec_legacy B.l D.k hl c E G := by
    dsimp only [G]
    delta sfCompactSupportFiniteIntegralFunctor
    exact (sfCompactSupportFiniteRealization_legacy B.l D.k hl c E).choose_spec
  obtain ⟨qG, hdelta⟩ := finiteIntegralFunctor_projections B.l E D.k hl c G hG
  apply normalizedProjection_functor_ext iY F G V L p hF
    (sfCompactSupportFiniteIntegralFunctor_obj B.l D.k hl c E) qF qG hgamma hdelta
  intro K K' a b hab
  let h := (exists_isDerivedLimit_and_iso
    (sfCompactSupportTerm B.l E c K'.obj)
    (sfCompactSupportTransition B.l E c K'.obj)).1
  let hm := Classical.choose_spec h
  exact derivedLimit_hom_ext_of_finite _ _ _ (Classical.choose hm)
    (Classical.choose (Classical.choose_spec hm))
    (Classical.choose_spec (Classical.choose_spec hm)) _
    (compactSupportTerm_hom_finite D B E f c (V K) K') a b hab


end WeilConjectures

namespace WeilConjectures.ConstructibleExceptionalCompositor
open ConstructibleExceptionalCoefficients
variable {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section OneArrow
variable {X Y : SixFunctorSpace D} (f : X ⟶ Y)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  (P : System.{u, u} B.l B.Qbar D B.different (f := f.hom.left))

end OneArrow

section TwoArrows
variable {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
  [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
  (P : System.{u, u} B.l B.Qbar D B.different (f := f.hom.left))
  (Q : System.{u, u} B.l B.Qbar D B.different (f := g.hom.left))
  (R : System.{u, u} B.l B.Qbar D B.different (f := (f ≫ g).hom.left))

end TwoArrows

end WeilConjectures.ConstructibleExceptionalCompositor
