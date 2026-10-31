/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineAdjunctionMaps
import all WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
import all WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
import all WeilConjectures.AlgebraicGeometry.ImmersionProjectionComparison.ImmersionProjectionSiteComparison
import all WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
import all WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorIntegrationSiteComparison
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineCounitTensor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Realization of the coordinate-line augmentation

Source: current blueprint, sk-prop-an, coordinate-line proof
(blueprint: lem-route-coordinate-line-augmentation-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.defProp false
set_option linter.style.emptyLine false
set_option linter.style.setOption false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
attribute [local instance high] GrothendieckTopology.W.monoidal
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
-- Keep the native derived functors' Abelian structures rather than imported cache aliases.
attribute [local instance 200000] sheafIsAbelian
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor DerivedCategory.canonicalTensorSymmetry
  AlgebraicGeometry.ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2 Etale.ordinaryFiniteColimitsOfShapeInt

namespace AlgebraicGeometry.ProEtale.CoordinateLine
-- Derived functors cache their coefficient-instance proofs. Share the same proofs
-- after removing local aliases, so the kernel compares the cached morphisms directly.
-- This only normalizes the proof term; ordinary kernel checking remains enabled.
open Lean Meta in
private meta def withSharedCoordinateBinders {α : Type} (xs : Array Expr)
    (k : MetaM α) : MetaM α := do
  let instances ← getLocalInstances
  let mut lctx ← getLCtx
  for x in xs do
    let decl ← x.fvarId!.getDecl
    let ty ← withLCtx lctx instances (abstractNestedProofs decl.type)
    lctx := lctx.modifyLocalDecl x.fvarId! fun decl => decl.setType ty
  withLCtx lctx instances k

open Lean Meta in
private meta def normalizeCoordinateInstancesAux (helpers : Array Name) :
    Nat → Expr → MetaM Expr
  | 0, proof => pure proof
  | fuel + 1, proof => do
    Meta.transform proof (skipConstInApp := true) (pre := fun expr => do
      if let .const name us := expr.getAppFn then
        if helpers.contains name then
          let ci ← getConstInfo name
          return .visit ((← instantiateValueLevelParams ci us (allowOpaque := true)).beta
            expr.getAppArgs)
      if expr.isLambda then
        return ← lambdaTelescope expr fun xs body => do
          withSharedCoordinateBinders xs do
            let body ← normalizeCoordinateInstancesAux helpers fuel body
            return .done (← mkLambdaFVars xs body)
      if ← AbstractNestedProofs.isNonTrivialProof expr then
        let ty ← inferType expr
        let env ← getEnv
        let classProof ← forallTelescopeReducing ty fun _ body => do
          return match body.getAppFn with
            | .const n _ => isClass env n
            | _ => false
        if classProof then
          let expr ← abstractProof expr (postprocessType := fun ty => abstractNestedProofs ty)
          return .done expr
      return .continue)

open Lean Meta in
private meta def normalizeCoordinateInstances (proof : Expr) (helpers : Array Name) :
    MetaM Expr := do
  let proof ← normalizeCoordinateInstancesAux helpers 64 proof
  if proof.hasSorry then
    throwError "Instance proof normalization left an unfinished proof"
  return proof

-- Prove changes of cached instance expressions by congruence before transporting
-- a proof. This is the same kernel-checked conversion used for projection associativity
-- in WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence.
private theorem coordinateProofHEq
    {P Q : Prop} (p : P) (q : Q) (h : P = Q) : HEq p q := by
  cases h
  rfl

open Lean Meta in
private meta partial def coordinateCongrHEq (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if ← isProp (← inferType a) then
    let hp ← coordinateCongrHEq (← inferType a) (← inferType b)
    let e ← mkAppM ``eq_of_heq #[hp]
    return ← mkAppM ``coordinateProofHEq #[a, b, e]
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    try
      let argsA := a.getAppArgs
      let argsB := b.getAppArgs
      let ct ← mkHCongrWithArity a.getAppFn argsA.size
      let mut ps := #[]
      for i in [:argsA.size] do
        let mut h ← coordinateCongrHEq argsA[i]! argsB[i]!
        if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
        ps := ps ++ #[argsA[i]!, argsB[i]!, h]
      let pf := mkAppN ct.proof ps
      if (← inferType pf).isHEq then return pf
      else return ← mkAppM ``heq_of_eq #[pf]
    catch _ => pure ()
  unless ← withTransparency .all (isDefEq a b) do
    throwError "Coordinate expressions differ: {a} and {b}"
  let a' ← withTransparency .all (whnf a)
  let b' ← withTransparency .all (whnf b)
  if a' != a || b' != b then
    return ← coordinateCongrHEq a' b'
  return ← mkHEqRefl a

open Lean Meta in
private meta def transportCoordinateApplications (proof : Expr) : MetaM Expr := do
  Meta.transform proof (skipConstInApp := true) (post := fun expr => do
    if let .const name _ := expr.getAppFn then
      if name.toString.endsWith ".tensor_trace_realization_with_maps" || name == ``Eq.trans then
        let mut ty ← inferType expr.getAppFn
        let mut result := expr.getAppFn
        for arg in expr.getAppArgs do
          let ty' ← whnf ty
          let .forallE _ domain body _ := ty'
            | throwError "Expected a comparison function"
          let mut arg := arg
          if ← isProp domain then
            let actual ← inferType arg
            if domain != actual then
              let he ← coordinateCongrHEq domain actual
              let eq ← mkAppM ``eq_of_heq #[he]
              arg ← mkAppM ``Eq.mpr #[eq, arg]
          result := mkApp result arg
          ty := body.instantiate1 arg
        return .done result
    return .continue)

open AffineLinePurity VectorIntegrationSite

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] AffineLinePurity.coefficientRing linePlus
  right affineTraceLineCompactification
  Etale.affineTraceOpenLeft
  Etale.ordinaryFiniteTwistedPullback Etale.ordinaryFiniteTensor Etale.derivedTensorRight
  Etale.derivedTensorWhiskeringLeftOpenImmersionLowerShriek
  Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar
  derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  projectionComparisonTensor
  Etale.ordinaryFinitePullback Etale.ordinaryFinitePushforward
  Etale.derivedTensorRightDerivedLowerStar
  Etale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
  Etale.derivedTensorRightDerivedLowerShriek
  Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

private theorem etale_symmetry_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T =
      ImmersionProjectionComparison.Etale.symmetry A T := by
  rfl

private theorem proetale_symmetry_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) :
    VectorIntegrationSite.symmetry (ModuleCat.{u + 1} A) T =
      ImmersionProjectionComparison.ProEtale.symmetry A T := by
  unfold VectorIntegrationSite.symmetry
  rfl

private theorem comparison_symmetry
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K W : Etale.DerivedCategoryModule A T) :
    (VectorIntegrationSite.comparison A T).map
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app K).app W) ≫
        (tensorComparison A T W K).hom =
      (tensorComparison A T K W).hom ≫
        (((VectorIntegrationSite.symmetry (ModuleCat.{u + 1} A) T).hom.app
          ((VectorIntegrationSite.comparison A T).obj K)).app
          ((VectorIntegrationSite.comparison A T).obj W)) := by
  rw [etale_symmetry_eq, proetale_symmetry_eq]
  simpa -implicitDefEqProofs only [tensorComparison, ImmersionProjectionComparison.comparisonTensor,
    ImmersionProjectionComparison.comparison, Iso.app_hom] using
      ImmersionProjectionComparison.comparisonTensor_symmetry A T K W

section GeometricProjection
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [Etale.UpperStarPreservesFlat B]
  {FC : B → B → Type w} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]

private theorem geometric_line_projection (T : Scheme.{u})
    (W : DerivedCategory (Sheaf (AffineSpace PUnit.{u + 1} T).smallEtaleTopology B))
    (K : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    ((Etale.projectionMapOfCompactification B (affineTraceLineCompactification T)).app W).app K =
      ((Etale.rightDerivedLowerStarProjectionMap B (ProjectiveLine T ↘ T)).app
        ((Etale.openImmersionLowerShriek B (ProjectiveLine.affineChart T)).mapDerivedCategory.obj
          W)).app K ≫
      (Etale.lowerStar B (ProjectiveLine T ↘ T)).rightDerivedFunctor.map
        (((Etale.derivedOpenImmersionLowerShriekProjectionIso B
          (ProjectiveLine.affineChart T)).inv.app W).app
          ((Etale.upperStar B (ProjectiveLine T ↘ T)).leftDerivedFunctor.obj K)) ≫
      (Etale.lowerStar B (ProjectiveLine T ↘ T)).rightDerivedFunctor.map
        ((Etale.openImmersionLowerShriek B
          (ProjectiveLine.affineChart T)).mapDerivedCategory.map
            (((Etale.derivedTensor B (AffineSpace PUnit.{u + 1} T)).obj W).map
              ((Etale.leftDerivedUpperStarComp B (ProjectiveLine.affineChart T)
                (ProjectiveLine T ↘ T) (AffineSpace PUnit.{u + 1} T ↘ T)
                (ProjectiveLine.affineChart_over T).symm).inv.app K))) := by
  rw [Etale.projectionMapOfCompactification_app_app]
  rw [Etale.leftDerivedUpperStarCompactificationIso_eq]
  rfl

end GeometricProjection

private theorem line_projection_expansion
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (W : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T))
    (K : Etale.DerivedCategoryModule A T) :
    ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)).app W).app K =
      ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
        (ProjectiveLine T ↘ T)).app ((Etale.affineTraceOpenLeft A T).obj W)).app K ≫
      (Etale.ordinaryFinitePushforward A (ProjectiveLine T ↘ T)).map
        (((Etale.derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A)
          (ProjectiveLine.affineChart T)).inv.app W).app
            ((Etale.ordinaryFinitePullback A (ProjectiveLine T ↘ T)).obj K)) ≫
      (Etale.ordinaryFinitePushforward A (ProjectiveLine T ↘ T)).map
        ((Etale.affineTraceOpenLeft A T).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)).obj
            W).map ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
              (ProjectiveLine.affineChart T) (ProjectiveLine T ↘ T)
              (AffineSpace PUnit.{u + 1} T ↘ T)
              (ProjectiveLine.affineChart_over T).symm).inv.app K))) := by
  with_unfolding_all
    simpa -implicitDefEqProofs only [Etale.affineTraceOpenLeft,
      Etale.ordinaryFinitePushforward, Etale.ordinaryFinitePullback] using
        geometric_line_projection (ModuleCat.{u + 1} A) T W K

private theorem coordinate_projection_eq
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule A T) :
    projection A N hA T K =
      (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app K).app
          ((Etale.affineTraceLineLeft A T).obj (line A N hA T))) ≫
        ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A)
          (affineTraceLineCompactification T)).app (line A N hA T)).app K ≫
        (Etale.affineTraceLineLeft A T).map
          (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
            (AffineSpace PUnit.{u + 1} T)).hom.app (line A N hA T)).app
              ((Etale.ordinaryFinitePullback A
                (AffineSpace PUnit.{u + 1} T ↘ T)).obj K)) := by
  unfold projection
  rw [line_projection_expansion]
  simp -implicitDefEqProofs only [Etale.affineTraceLineLeft, Functor.comp_obj,
    Category.assoc]

private theorem comparison_pullback_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    comparisonOpenDerivedPullbackIso A f = VectorIntegrationSite.pullback A f := by
  unfold comparisonOpenDerivedPullbackIso VectorIntegrationSite.pullback geoP1PullComparison
  simp -implicitDefEqProofs only [supportComparison_eq]
  apply Iso.ext
  ext K
  simp -implicitDefEqProofs only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]

private def ordinaryProjection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :=
  (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app H).app
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj W)) ≫
    ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app W).app H ≫
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app
        ((Etale.ordinaryFinitePullback A f).obj H))

private theorem tensorPullback_symmetry
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y) :
    (VectorIntegrationSite.comparison A X).map
        (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app W).app
          ((Etale.ordinaryFinitePullback A f).obj H)) ≫
        (tensorPullbackComparison A f H W).hom =
      (comparisonOpenTensorIso A f W H).hom ≫
        (((VectorIntegrationSite.symmetry (ModuleCat.{u + 1} A) X).hom.app
          ((VectorIntegrationSite.comparison A X).obj W)).app
            ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
              ((VectorIntegrationSite.comparison A Y).obj H))) := by
  unfold tensorPullbackComparison comparisonOpenTensorIso
  rw [comparison_pullback_eq]
  simp -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  have hs := comparison_symmetry A X W ((Etale.ordinaryFinitePullback A f).obj H)
  unfold tensorComparison at hs ⊢
  rw [← Category.assoc, hs, Category.assoc]
  simp -implicitDefEqProofs only [Category.assoc, Iso.app_hom]
  apply congrArg (fun z ↦
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) W).hom.app
        ((Etale.ordinaryFinitePullback A f).obj H) ≫ z)
  exact ((VectorIntegrationSite.symmetry (ModuleCat.{u + 1} A) X).hom.app
    ((VectorIntegrationSite.comparison A X).obj W)).naturality
      ((VectorIntegrationSite.pullback A f).hom.app H) |>.symm

private theorem paste_symmetric_square
    {D : Type*} [Category* D] {X₀ X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ Z₁ Z₂ : D}
    {a : X₀ ⟶ X₁} {p : X₁ ⟶ X₂} {b : X₂ ⟶ X₃} {t : X₃ ⟶ X₄} {q : X₄ ⟶ X₅}
    {c : X₁ ⟶ Y₁} {d : Y₁ ⟶ Y₂} {e : Y₂ ⟶ X₄}
    {f : X₀ ⟶ Z₁} {g : Z₁ ⟶ Z₂} {h : Z₂ ⟶ Y₂} {s : Z₁ ⟶ Y₁}
    (hp : p ≫ b ≫ t = c ≫ d ≫ e)
    (hf : a ≫ c = f ≫ s) (hb : g ≫ h = s ≫ d) :
    a ≫ p ≫ b ≫ t ≫ q = f ≫ g ≫ h ≫ e ≫ q := by
  rw [reassoc_of% hp, reassoc_of% hf, ← reassoc_of% hb]

private theorem transport_symmetric_square
    {E₀ E₁ P₀ P₁ : Type*} [Category* E₀] [Category* E₁]
    [Category* P₀] [Category* P₁]
    (Cy : E₁ ⥤ P₁) (Fe : E₀ ⥤ E₁) (Fp : P₀ ⥤ P₁) (Cx : E₀ ⥤ P₀)
    {L S : E₀} {V U : E₁} {R R' : P₀} {Y₁ Y₂ Z₁ Z₂ : P₁}
    {a : V ⟶ U} {p : U ⟶ Fe.obj L} {σ : L ⟶ S}
    {bL : Cy.obj (Fe.obj L) ⟶ Fp.obj (Cx.obj L)}
    {bS : Cy.obj (Fe.obj S) ⟶ Fp.obj (Cx.obj S)}
    {tp : Cx.obj L ⟶ R} {tpc : Cx.obj S ⟶ R'} {sp : R ⟶ R'}
    {c : Cy.obj U ⟶ Y₁} {d : Y₁ ⟶ Y₂} {e : Y₂ ⟶ Fp.obj R}
    {f : Cy.obj V ⟶ Z₁} {g : Z₁ ⟶ Z₂} {h : Z₂ ⟶ Y₂} {s : Z₁ ⟶ Y₁}
    (hp : Cy.map p ≫ bL ≫ Fp.map tp = c ≫ d ≫ e)
    (hn : Cy.map (Fe.map σ) ≫ bS = bL ≫ Fp.map (Cx.map σ))
    (ht : Cx.map σ ≫ tpc = tp ≫ sp)
    (hf : Cy.map a ≫ c = f ≫ s) (hb : g ≫ h = s ≫ d) :
    Cy.map (a ≫ p ≫ Fe.map σ) ≫ bS ≫ Fp.map tpc =
      f ≫ g ≫ h ≫ e ≫ Fp.map sp := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← Fp.map_comp, ht, Fp.map_comp]
  try simp only [Category.assoc]
  exact paste_symmetric_square hp hf hb

-- The inferred proposition retains precisely the native instance arguments of the
-- pasted square; restating it explicitly triggers expensive kernel conversions.
private def compact_coefficient_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (W : Etale.DerivedCategoryModule A X) (H : Etale.DerivedCategoryModule A Y)
    (hW : DerivedCategory.TStructure.t.plus W)
    (hS : DerivedCategory.TStructure.t.plus
      (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.ordinaryFinitePullback A f).obj H)).obj W)) := by
  let B := ModuleCat.{u + 1} A
  let Fe := Etale.rightDerivedLowerShriekOfCompactification B c
  let Fp := rightDerivedLowerShriekOfCompactification B c
  let Cx := VectorIntegrationSite.comparison A X
  let Cy := VectorIntegrationSite.comparison A Y
  let σ := ((Etale.derivedTensorSymmetry B X).app W).app
    ((Etale.ordinaryFinitePullback A f).obj H)
  have hD : DerivedCategory.TStructure.t.plus (projectionComparisonTensor A (f := f) W H) :=
    DerivedCategory.TStructure.t.plus.prop_of_iso σ.symm hS
  have hp := compact_projection_square A c W H hW hD
  have hn := (compactSupportSiteComparison A c).inv.naturality
    (X := ⟨projectionComparisonTensor A (f := f) W H, hD⟩)
    (Y := ⟨_, hS⟩) (ObjectProperty.homMk σ.hom)
  change Cy.map (Fe.map σ.hom) ≫
      (compactSupportSiteComparison A c).inv.app ⟨_, hS⟩ =
    (compactSupportSiteComparison A c).inv.app ⟨_, hD⟩ ≫ Fp.map (Cx.map σ.hom) at hn
  have ht := tensorPullback_symmetry A f W H
  have hf := comparison_symmetry A Y H (Fe.obj W)
  have hb := ((VectorIntegrationSite.symmetry B Y).hom.app (Cy.obj H)).naturality
    ((compactSupportSiteComparison A c).inv.app ⟨W, hW⟩)
  unfold tensorComparison at hf
  with_unfolding_all
    exact transport_symmetric_square Cy Fe Fp Cx hp hn
      (by simpa only [Cx, σ, Iso.app_hom] using ht) hf hb

section ExactUnit
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] CochainComplex.singleFunctors
universe u₁ u₂
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
private theorem exact_unit_normalization :
    let := F.mapDerivedCategoryOplaxMonoidal
    F.mapDerivedCategory.map (DerivedCategory.singleFunctorObjUnitIso C).hom ≫
        Functor.OplaxMonoidal.η F.mapDerivedCategory =
      (F.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ C) ≫
        (DerivedCategory.singleFunctor D 0).map (Functor.Monoidal.εIso F).inv ≫
        (DerivedCategory.singleFunctorObjUnitIso D).hom := by
  have := DerivedCategory.isIso_ε_Qh C
  have := DerivedCategory.isIso_ε_Qh D
  change F.mapDerivedCategory.map (DerivedCategory.singleFunctorObjUnitIso C).hom ≫
      (F.mapDerivedCategory.map (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := C))) ≫
        F.mapDerivedCategoryFactorsh.hom.app (𝟙_ _) ≫
        DerivedCategory.Qh.map (Functor.OplaxMonoidal.η
          (F.mapHomotopyCategory (.up ℤ))) ≫
        inv (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := D)))) = _
  simp -implicitDefEqProofs only [DerivedCategory.singleFunctorObjUnitIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  simp -implicitDefEqProofs only [asIso_inv, Functor.map_inv, IsIso.inv_hom_id_assoc]
  erw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp -implicitDefEqProofs only [Functor.mapHomotopyCategory_η, Functor.mapCochainComplex_η,
    Functor.mapDerivedCategorySingleFunctor, Functor.mapCochainComplexεIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    NatTrans.comp_app, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.id_comp, Category.comp_id, Category.assoc]
  have hqC : (Functor.Monoidal.εIso (HomotopyCategory.quotient C (.up ℤ))).inv =
      𝟙 _ := rfl
  have hqD : (Functor.Monoidal.εIso (HomotopyCategory.quotient D (.up ℤ))).inv =
      𝟙 _ := rfl
  simp -implicitDefEqProofs only [hqC, hqD, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Functor.map_inv, IsIso.inv_hom_id_assoc]
  have hn := (DerivedCategory.singleFunctorIsoCompQ D 0).hom.naturality
    (Functor.Monoidal.εIso F).inv
  erw [reassoc_of% hn]
  simp -implicitDefEqProofs only [Iso.inv_hom_id_app_assoc]
  simp -implicitDefEqProofs only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, NatTrans.id_app]
  have hc :
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app
        (𝟙_ (CochainComplex C ℤ))) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app
        (𝟙_ (CochainComplex C ℤ))) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [reassoc_of% hc]
  change _ = _
  have hn₂ := (DerivedCategory.quotientCompQhIso D).inv.naturality
    ((CochainComplex.singleFunctor D 0).map (Functor.Monoidal.εIso F).inv)
  erw [reassoc_of% hn₂]
  have hn₁ := (DerivedCategory.quotientCompQhIso D).inv.naturality
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app (𝟙_ C))
  erw [reassoc_of% hn₁]
  simp -implicitDefEqProofs only [DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, NatTrans.id_app, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  repeat' erw [CategoryTheory.Functor.map_id]
  repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
  erw [Functor.map_comp]
  simp -implicitDefEqProofs only [Category.assoc, Iso.app_hom]
  rfl

private theorem exact_tensor_singleUnit
    (K : DerivedCategory C) :
    (F.mapDerivedCategoryTensorComparison.app K).app
        ((DerivedCategory.singleFunctor C 0).obj (𝟙_ C)) ≫
      F.mapDerivedCategory.obj K ◁
        ((F.mapDerivedCategorySingleFunctor 0).hom.app (𝟙_ C) ≫
          (DerivedCategory.singleFunctor D 0).map (Functor.Monoidal.εIso F).inv ≫
          (DerivedCategory.singleFunctorObjUnitIso D).hom) ≫
      (ρ_ (F.mapDerivedCategory.obj K)).hom =
    F.mapDerivedCategory.map
      ((K ◁ (DerivedCategory.singleFunctorObjUnitIso C).hom) ≫ (ρ_ K).hom) := by
  let := F.mapDerivedCategoryOplaxMonoidal
  rw [← exact_unit_normalization F]
  simp -implicitDefEqProofs only [whiskerLeft_comp, Category.assoc]
  have hn := (F.mapDerivedCategoryTensorComparison.app K).naturality
    (DerivedCategory.singleFunctorObjUnitIso C).hom
  change F.mapDerivedCategory.map (K ◁ (DerivedCategory.singleFunctorObjUnitIso C).hom) ≫
      (F.mapDerivedCategoryTensorComparison.app K).app (𝟙_ _) =
    (F.mapDerivedCategoryTensorComparison.app K).app _ ≫
      F.mapDerivedCategory.obj K ◁
        F.mapDerivedCategory.map (DerivedCategory.singleFunctorObjUnitIso C).hom at hn
  rw [← reassoc_of% hn]
  rw [← F.mapDerivedCategoryOplaxMonoidal_δ]
  rw [Functor.OplaxMonoidal.right_unitality_hom, ← F.mapDerivedCategory.map_comp]

private theorem exact_tensor_comparison (K M : DerivedCategory C) :
    let i := Functor.isoWhiskerLeft ((curriedTensor (DerivedCategory C)).obj K)
        F.leftDerivedFunctorIsoMapDerivedCategory.symm ≪≫
      (asIso F.leftDerivedTensorComparison).app K ≪≫
      Functor.isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory
        ((curriedTensor (DerivedCategory D)).obj (F.leftDerivedFunctor.obj K)) ≪≫
      Functor.isoWhiskerLeft F.mapDerivedCategory
        ((curriedTensor (DerivedCategory D)).mapIso
          (F.leftDerivedFunctorIsoMapDerivedCategory.app K))
    i.hom.app M = (F.mapDerivedCategoryTensorComparison.app K).app M := by
  dsimp only
  rw [Functor.mapDerivedCategoryTensorComparison_app_app]
  simp -implicitDefEqProofs only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, asIso_hom, Functor.mapIso_hom, tensorHom_def']
  rfl

end ExactUnit

section GeometricUnit
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]

private theorem geometric_tensor_comparison (T : Scheme.{u})
    [(comparisonUpperStar B T).PreservesFlat]
    (K W : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B K).hom.app W =
      (((comparisonUpperStar B T).mapDerivedCategoryTensorComparison.app K).app W) := by
  unfold derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
  simpa -implicitDefEqProofs only [Etale.derivedTensor, derivedTensor, Iso.app_hom] using
    exact_tensor_comparison (comparisonUpperStar B T) K W

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] CochainComplex.singleFunctors

private theorem geometric_unit_comparison (T : Scheme.{u})
    [(comparisonUpperStar B T).PreservesFlat]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B K).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ (Sheaf T.smallEtaleTopology B))) ≫
      (coefficientRightUnit B T ((comparisonUpperStar B T).mapDerivedCategory.obj K)).hom =
    (comparisonUpperStar B T).mapDerivedCategory.map
      ((((Etale.derivedTensor B T).obj K).mapIso
          (Etale.singleFunctorObjUnitIso B T)).hom ≫
        (Etale.derivedTensorRightUnitor B T K).hom) := by
  rw [geometric_tensor_comparison]
  unfold coefficientRightUnit coefficientUnitIso
  have h := exact_tensor_singleUnit (comparisonUpperStar B T) K
  simp -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Etale.derivedTensorRightUnitor, Etale.derivedTensor, derivedTensor,
    curriedTensor_obj_map, Category.assoc, Etale.singleFunctorObjUnitIso,
    Etale.singleFunctorObjIsoQh, DerivedCategory.singleFunctorObjUnitIso] at h ⊢
  exact h

end GeometricUnit
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] CochainComplex.singleFunctors

private theorem tensor_unit_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (K : Etale.DerivedCategoryModule A T) :
    (tensorComparison A T K (Etale.ordinaryFiniteUnit A T)).hom ≫
      (moduleRightUnit A T ((VectorIntegrationSite.comparison A T).obj K)).hom =
    (VectorIntegrationSite.comparison A T).map
      (Etale.derivedTensorSingleUnitIso K).hom := by
  have h := geometric_unit_comparison (ModuleCat.{u + 1} A) T K
  erw [Functor.mapIso_hom] at h
  unfold moduleRightUnit Etale.derivedTensorSingleUnitIso
  erw [Iso.trans_hom, Functor.mapIso_hom]
  simp -implicitDefEqProofs only [tensorComparison, Iso.app_hom, Functor.comp_obj,
    VectorIntegrationSite.comparison, geoP1Comparison, Etale.ordinaryFiniteUnit,
    Etale.ordinaryFiniteDegreeZero, Etale.ordinaryFiniteConstant]
  with_unfolding_all exact h

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] Triangulated.TStructure.plus
  Triangulated.TStructure.minus Triangulated.TStructure.bounded
  Functor.mapDerivedCategoryPlus
  right etaleCoefficient etaleSource ordinarySourceObject
  Etale.affineTraceOpenAdjunction Etale.affineTraceOpenLeft
  Etale.ordinaryFinitePullback Etale.ordinaryFinitePushforward
private theorem open_restriction_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openProjectionRestrictionComparison A j = VectorIntegrationSite.pullback A j := by
  unfold openProjectionRestrictionComparison VectorIntegrationSite.pullback geoP1PullComparison
  apply Iso.ext
  ext K
  simp -implicitDefEqProofs only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]

private theorem restrictTrace_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    (W : Etale.DerivedCategoryModule A (ProjectiveLine T))
    (hW : DerivedCategory.TStructure.t.plus W)
    (hJ : DerivedCategory.TStructure.t.plus
      ((Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).obj W))
    (t : (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine T ↘ T)).rightDerivedFunctor.obj
      ((VectorIntegrationSite.comparison A (ProjectiveLine T)).obj W) ⟶ unit A T) :
    (compactSupportSiteComparison A (affineTraceLineCompactification T)).inv.app
        ⟨_, hJ⟩ ≫ restrictTrace A T W t =
      (VectorIntegrationSite.comparison A T).map
        ((Etale.ordinaryFinitePushforward A (ProjectiveLine T ↘ T)).map
          ((Etale.affineTraceOpenAdjunction A T).counit.app W)) ≫
        (directImage A (ProjectiveLine T ↘ T) ⟨W, hW⟩).hom ≫ t := by
  let B := ModuleCat.{u + 1} A
  let j := ProjectiveLine.affineChart T
  let q := ProjectiveLine T ↘ T
  let J := (Etale.openImmersionLowerShriek B j).mapDerivedCategory
  let Q := (lowerStar B q).rightDerivedFunctor
  have ho := openCounitComparison A j W
  rw [open_restriction_eq] at ho
  have hn := pushComparison_naturality A q ((Etale.affineTraceOpenAdjunction A T).counit.app W)
  rw [directImage_eq_push A q ⟨W, hW⟩]
  rw [compact_comparison_inv A (affineTraceLineCompactification T) ⟨_, hJ⟩]
  rw [← pushComparison_eq]
  unfold restrictTrace
  dsimp only [affineTraceLineCompactification, Functor.comp_map, lineLeft]
  simp -implicitDefEqProofs only [Category.assoc]
  change geoP1PushComparison A q (J.obj _) ≫
      Q.map ((openProjectionExtensionComparison A j).hom.app _) ≫
      Q.map ((openImmersionLowerShriek B j).mapDerivedCategory.map
        ((pullback A j).hom.app W)) ≫
      Q.map ((openAdjunction A j).counit.app ((VectorIntegrationSite.comparison A _).obj W)) ≫
      t = _
  have hoQ := congrArg Q.map ho
  simp -implicitDefEqProofs only [Functor.map_comp, Category.assoc] at hoQ
  have he := congrArg
    (fun v ↦ geoP1PushComparison A q (J.obj ((Etale.ordinaryFinitePullback A j).obj W)) ≫
      v ≫ t) hoQ.symm
  calc
    _ = (geoP1PushComparison A q (J.obj ((Etale.ordinaryFinitePullback A j).obj W)) ≫
        Q.map ((VectorIntegrationSite.comparison A (ProjectiveLine T)).map
          ((Etale.affineTraceOpenAdjunction A T).counit.app W))) ≫ t := by
      simpa -implicitDefEqProofs only [Category.assoc, Etale.affineTraceOpenAdjunction,
        Etale.ordinaryFinitePullback] using he
    _ = _ := by
      simpa -implicitDefEqProofs only [Category.assoc, Functor.comp_obj, Functor.id_obj,
        Etale.affineTraceOpenLeft, geoP1Comparison, geoP1Pushforward, q, j, B, J, Q,
        VectorIntegrationSite.comparison] using congrArg (fun v ↦ v ≫ t) hn.symm

private theorem integration_comparison
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) [IsNoetherian T]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hT : IsUnit (P.coefficients.l : Γ(T, ⊤))) :
    (compactSupportSiteComparison (Ring P) (affineTraceLineCompactification T)).inv.app
        ⟨line (Ring P) (P.coefficients.l ^ (r + 1)) hA T,
          (ordinaryPullback_bounded (Ring P) (ProjectiveLine.affineChart T) _
            (shiftedLine_bounded (Ring P) (P.coefficients.l ^ (r + 1)) hA
              (ProjectiveLine T))).1⟩ ≫
      AffineLinePurity.integration P.coefficients.l P.extension (P.level - 1) T r hA hT =
    (VectorIntegrationSite.comparison (Ring P) T).map
      (integration (Ring P) (P.coefficients.l ^ (r + 1)) hA T
        (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
        (by simpa -implicitDefEqProofs only [Nat.cast_pow] using hT.pow (r + 1))) := by
  have hs := restrictTrace_comparison (Ring P) T
    ((Etale.ordinaryFiniteLine (Ring P) (P.coefficients.l ^ (r + 1)) hA
      (ProjectiveLine T))⟦(2 : ℤ)⟧)
    (shiftedLine_bounded (Ring P) (P.coefficients.l ^ (r + 1)) hA (ProjectiveLine T)).1
    (ordinaryPullback_bounded (Ring P) (ProjectiveLine.affineChart T) _
      (shiftedLine_bounded (Ring P) (P.coefficients.l ^ (r + 1)) hA
        (ProjectiveLine T))).1
    (projectiveTrace P.coefficients.l P.extension (P.level - 1) T hT
      (infinityCartier T) r hA)
  have ht := (projectiveComparison P.coefficients.l P.extension (P.level - 1) T hT
    (infinityCartier T) r hA).2.1
  unfold AffineLinePurity.integration
  simp -implicitDefEqProofs only [coefficient_comparison_eq, etaleCoefficient_eq,
    eqToIso_refl, Iso.refl_hom,
    eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  rw [hs]
  dsimp only [linePlus] at ht
  erw [ht]
  unfold integration
  exact ((VectorIntegrationSite.comparison (Ring P) T).map_comp _ _).symm

private def projectionNatural
    (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    [UpperStarPreservesFlat V] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V)) :
    (derivedTensor V Y).flip.obj
        ((rightDerivedLowerShriekOfCompactification V c).obj F) ⟶
      (upperStar V f).leftDerivedFunctor ⋙ (derivedTensor V X).flip.obj F ⋙
        rightDerivedLowerShriekOfCompactification V c :=
  (symmetry V Y).hom.flipApp _ ≫
    (projectionMapOfCompactification V c).app F ≫
      Functor.whiskerLeft (upperStar V f).leftDerivedFunctor
        (Functor.whiskerRight ((symmetry V X).hom.app F)
          (rightDerivedLowerShriekOfCompactification V c))

private theorem projection_natural
    (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    [UpperStarPreservesFlat V] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V))
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)} (h : K ⟶ L) :
    ((derivedTensor V Y).map h).app
        ((rightDerivedLowerShriekOfCompactification V c).obj F) ≫
      VectorIntegrationSite.projection V c F L =
      VectorIntegrationSite.projection V c F K ≫ (rightDerivedLowerShriekOfCompactification V c).map
        (((derivedTensor V X).map ((upperStar V f).leftDerivedFunctor.map h)).app F) := by
  have he (Z : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)) :
      (projectionNatural V c F).app Z = VectorIntegrationSite.projection V c F Z := by
    unfold projectionNatural VectorIntegrationSite.projection
    rfl
  have hn := (projectionNatural V c F).naturality h
  rw [he, he] at hn
  exact hn

private theorem coefficientRightUnit_natural
    (V : Type v) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V] [MonoidalPreadditive V]
    [SymmetricCategory V] [MonoidalClosed V] [Abelian.HasFunctorialFlatResolution V]
    (Y : Scheme.{u})
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) V)} (h : K ⟶ L) :
    ((derivedTensor V Y).map h).app _ ≫ (coefficientRightUnit V Y L).hom =
      (coefficientRightUnit V Y K).hom ≫ h := by
  have hn := ((derivedTensor V Y).map h).naturality (coefficientUnitIso V Y).hom
  unfold coefficientRightUnit
  simp -implicitDefEqProofs only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← hn, Category.assoc]
  simpa -implicitDefEqProofs only [derivedTensor, curriedTensor, Category.assoc] using
    congrArg (fun z ↦ ((derivedTensor V Y).obj K).map (coefficientUnitIso V Y).hom ≫ z)
      (rightUnitor_naturality h)

set_option allowUnsafeReducibility true in
attribute [local reducible] projectionSourceObject projectionTargetObject

private theorem projectionTensorTrace_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))}
    (h : K ⟶ L)
    (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj F ⟶
      unit A Y)
    (hK : ProjectionInvertible A c F K) (hL : ProjectionInvertible A c F L) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map h)).app F) ≫
      projectionTensorTrace A c F L t hL = projectionTensorTrace A c F K t hK ≫ h := by
  let Q := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let T := derivedTensor (ModuleCat.{u + 1} A) Y
  let a := ((derivedTensor (ModuleCat.{u + 1} A) X).map
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map h)).app F
  let b := (T.map h).app (Q.obj F)
  have hp := projection_natural (ModuleCat.{u + 1} A) c F h
  unfold ProjectionInvertible at hK hL
  let := hK
  let := hL
  have hi : Q.map a ≫ inv (VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c F L) =
      inv (VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c F K) ≫ b := by
    symm
    apply (IsIso.inv_comp_eq (VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c F K)).2
    change b = VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c F K ≫ Q.map a ≫
      inv (VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c F L)
    rw [← Category.assoc, ← hp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  unfold projectionTensorTrace inverseProjection
  dsimp only [Iso.symm_hom, asIso_inv]
  change Q.map a ≫ (inv (VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c F L) ≫
    (T.obj L).map t ≫ (moduleRightUnit A Y L).hom) =
      (inv (VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c F K) ≫
        (T.obj K).map t ≫ (moduleRightUnit A Y K).hom) ≫ h
  rw [← Category.assoc, hi]
  simp -implicitDefEqProofs only [Category.assoc]
  have ht := ((T.map h).naturality t).symm
  change b ≫ (T.obj L).map t = (T.obj K).map t ≫ (T.map h).app _ at ht
  rw [reassoc_of% ht]
  unfold moduleRightUnit
  have hr := coefficientRightUnit_natural (ModuleCat.{u + 1} A) Y h
  exact congrArg (fun z ↦ inv (VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c F K) ≫
    (T.obj K).map t ≫ z) hr

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] AffineLinePurity.coefficientRing linePlus source etaleSource
  ordinarySourceObject proSourceObject
  projectionSourceObject etaleCoefficient

private theorem slide_identities {D : Type*} [Category* D]
    {X Y Z : D} (a : X ⟶ Y) (b : Y ⟶ Z) :
    a ≫ b ≫ 𝟙 Z = a ≫ 𝟙 Y ≫ b := by
  simp only [Category.comp_id, Category.id_comp]

private theorem sourceComparison_hom_factor
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u})
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))))
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T)
    (eK : (VectorIntegrationSite.comparison (Scheme.finiteTateCoefficient l E n) T).obj Ke ≅ K) :
    (sourceComparison l E n T r hA K Ke eK).hom =
      (sourceComparison l E n T r hA
        ((VectorIntegrationSite.comparison (Scheme.finiteTateCoefficient l E n) T).obj Ke)
        Ke (Iso.refl _)).hom ≫
      ((derivedTensor (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
        (AffineSpace PUnit.{u + 1} T)).map
        ((upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
          (AffineSpace PUnit.{u + 1} T ↘ T)).leftDerivedFunctor.map eK.hom)).app
        (coefficient l E n T r hA) := by
  unfold sourceComparison realizedTensorComparison
  dsimp only [source, projectionSourceObject, coefficient]
  simp -implicitDefEqProofs only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    id_eq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Functor.mapIso_refl,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
    Iso.app_hom, Category.assoc]

  exact slide_identities _ _

private theorem sourceComparison_refl
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (T : Scheme.{u})
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) T) :
    (sourceComparison l E n T r hA
      ((VectorIntegrationSite.comparison (Scheme.finiteTateCoefficient l E n) T).obj Ke)
      Ke (Iso.refl _)).hom =
    (tensorPullbackComparison (Scheme.finiteTateCoefficient l E n)
      (AffineSpace PUnit.{u + 1} T ↘ T) Ke (etaleCoefficient l E n T r hA)).hom := by
  unfold sourceComparison realizedTensorComparison
  dsimp only [source, projectionSourceObject, coefficient]
  simp -implicitDefEqProofs only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    id_eq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Functor.mapIso_refl,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
    Iso.app_hom, Category.assoc]
  exact Category.comp_id _

set_option maxHeartbeats 1000000 in
-- Unfolding coordinate comparisons traverses the derived tensor instance data.
private theorem sourceCoordinates_hom
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (Ke : Etale.DerivedCategoryModule (Ring P) T) :
    (sourceCoordinates P T r hA Ke).hom =
      𝟙 ((right (Ring P) (P.coefficients.l ^ (r + 1)) hA T).obj Ke) := by
  unfold sourceCoordinates rightCoordinates
  simp -implicitDefEqProofs only [id_eq, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.id_comp, Category.comp_id]
  simp -implicitDefEqProofs only [right, Etale.ordinaryFiniteTwistedPullback,
    Etale.derivedTensorRight, Functor.comp_obj, Functor.flip]

private theorem tensor_trace_realization_with_maps
    {E D : Type*} [Category* E] [Category* D] {L : D}
    (C : E ⥤ D) (Te : E ⥤ E ⥤ E) (Tp : D ⥤ D ⥤ D)
    (K V U S : E) (W R : D)
    (βV : C.obj ((Te.obj K).obj V) ⟶ (Tp.obj (C.obj K)).obj (C.obj V))
    (βU : C.obj ((Te.obj K).obj U) ⟶ (Tp.obj (C.obj K)).obj (C.obj U))
    (pe : (Te.obj K).obj V ≅ S)
    (pp : (Tp.obj (C.obj K)).obj W ≅ R)
    (d₁ : C.obj S ⟶ L) (d₂ : L ⟶ R) (b : C.obj V ⟶ W)
    (t : V ⟶ U) (τ : W ⟶ C.obj U)
    (ue : (Te.obj K).obj U ⟶ K)
    (up : (Tp.obj (C.obj K)).obj (C.obj U) ⟶ C.obj K)
    (ε : S ⟶ K)
    (a : (Te.obj K).obj V ⟶ S) (q : (Tp.obj (C.obj K)).obj W ⟶ R)
    (hs : C.map a ≫ d₁ ≫ d₂ = βV ≫ (Tp.obj (C.obj K)).map b ≫ q)
    (ht : b ≫ τ = C.map t)
    (hn : C.map ((Te.obj K).map t) ≫ βU =
      βV ≫ (Tp.obj (C.obj K)).map (C.map t))
    (hu : βU ≫ up = C.map ue)
    (he : pe.hom ≫ ε = (Te.obj K).map t ≫ ue)
    (hpe : pe.hom = a) (hpp : pp.hom = q) :
    d₁ ≫ d₂ ≫ pp.inv ≫ (Tp.obj (C.obj K)).map τ ≫ up = C.map ε := by
  apply (cancel_epi (C.map pe.hom)).mp
  have hs' : C.map pe.hom ≫ d₁ ≫ d₂ = βV ≫ (Tp.obj (C.obj K)).map b ≫ pp.hom := by
    rw [hpe, hpp]
    exact hs
  try simp only [Category.assoc]
  rw [reassoc_of% hs']
  simp -implicitDefEqProofs only [Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, ht]
  rw [← reassoc_of% hn, hu, ← C.map_comp, ← he, C.map_comp]

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] ProjectionInvertible projectionSourceObject
  projectionTargetObject

private theorem inverse_projection_forward
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (W : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (hi : ProjectionInvertible A c W K) :
    (inverseProjection A c W K hi).inv =
      VectorIntegrationSite.projection (ModuleCat.{u + 1} A) c W K := by
  unfold inverseProjection
  rfl

section GeometricProjectionExpansion
variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]

private theorem geometric_image_projection_expansion {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (W : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (hW : DerivedCategory.TStructure.t.plus W) :
    VectorIntegrationSite.projection B c
        ((comparisonUpperStar B X).mapDerivedCategory.obj W)
        ((comparisonUpperStar B Y).mapDerivedCategory.obj K) =
      ((VectorIntegrationSite.symmetry B Y).hom.app
          ((comparisonUpperStar B Y).mapDerivedCategory.obj K)).app
        ((DerivedCategory.Plus.ι ⋙ (comparisonUpperStar B X).mapDerivedCategory ⋙
          rightDerivedLowerShriekOfCompactification B c).obj ⟨W, hW⟩) ≫
        ((projectionMapOfCompactification B c).app
          ((comparisonUpperStar B X).mapDerivedCategory.obj W)).app
            ((comparisonUpperStar B Y).mapDerivedCategory.obj K) ≫
        (rightDerivedLowerShriekOfCompactification B c).map
          (((VectorIntegrationSite.symmetry B X).hom.app
            ((comparisonUpperStar B X).mapDerivedCategory.obj W)).app
              ((upperStar B f).leftDerivedFunctor.obj
                ((comparisonUpperStar B Y).mapDerivedCategory.obj K))) := by
  unfold VectorIntegrationSite.projection
  rfl

end GeometricProjectionExpansion

set_option linter.style.multiGoal false in
set_option maxHeartbeats 1000000 in
-- The concrete derived comparison has large cached instance arguments.
private theorem core_realization
    (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T] (hN : 0 < N) (hT : IsUnit (N : Γ(T, ⊤)))
    (Ke : Etale.DerivedCategoryModule A T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T Ke)
    (hW : DerivedCategory.TStructure.t.plus (line A N hA T))
    (hS : DerivedCategory.TStructure.t.plus ((right A N hA T).obj Ke))
    (t : (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)).obj
        ((VectorIntegrationSite.comparison A _).obj (line A N hA T)) ⟶ unit A T)
    (ht : (compactSupportSiteComparison A (affineTraceLineCompactification T)).inv.app
        ⟨line A N hA T, hW⟩ ≫ t =
      (VectorIntegrationSite.comparison A T).map (integration A N hA T hN hT))
    (hi : ProjectionInvertible A (affineTraceLineCompactification T)
      ((VectorIntegrationSite.comparison A _).obj (line A N hA T))
      ((VectorIntegrationSite.comparison A T).obj Ke)) :
    (compactSupportSiteComparison A (affineTraceLineCompactification T)).inv.app
        ⟨(right A N hA T).obj Ke, hS⟩ ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (affineTraceLineCompactification T)).map
          (tensorPullbackComparison A (AffineSpace PUnit.{u + 1} T ↘ T)
            Ke (line A N hA T)).hom ≫
      projectionTensorTrace A (affineTraceLineCompactification T)
        ((VectorIntegrationSite.comparison A _).obj (line A N hA T))
        ((VectorIntegrationSite.comparison A T).obj Ke) t hi =
    (VectorIntegrationSite.comparison A T).map
      ((adjunction A N hA T hN hT).counit.app Ke) := by
  run_tac Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let h ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType)
    g.setTag h.mvarId!.name
    Lean.Elab.Tactic.replaceMainGoal [h.mvarId!, g]
  · let c := affineTraceLineCompactification T
    let W := line A N hA T
    let C := VectorIntegrationSite.comparison A T
    let Fe := Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let Fp := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let CK := C.obj Ke
    let S := ((Etale.derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj Ke)).obj W
    obtain ⟨pf, hp, hc⟩ := coordinate_line_counit_tensor A N hA T hN hT Ke hKe
    have hproj : ordinaryProjection A c W Ke = projection A N hA T Ke := by
      dsimp only [ordinaryProjection, c, W]
      exact (coordinate_projection_eq A N hA T Ke).symm
    have hpe : pf.hom = ordinaryProjection A c W Ke := hp.trans hproj.symm
    have he : pf.hom ≫ (adjunction A N hA T hN hT).counit.app Ke =
        ((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj Ke).map
          (integration A N hA T hN hT) ≫ (Etale.derivedTensorSingleUnitIso Ke).hom := by
      rw [hc]
      simp -implicitDefEqProofs only [Iso.hom_inv_id_assoc, Etale.ordinaryFiniteTensor]
    let a := (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app Ke).app
        (Fe.obj W)) ≫ ((Etale.projectionMapOfCompactification
          (ModuleCat.{u + 1} A) c).app W).app Ke ≫
        Fe.map (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
          (AffineSpace PUnit.{u + 1} T)).app W).app
          ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj Ke)).hom
    have hn := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) Ke).hom.naturality (integration A N hA T hN hT)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    have hsq := compact_coefficient_square A c W Ke hW hS
    have heproj := inverse_projection_forward A c
      ((VectorIntegrationSite.comparison A (AffineSpace PUnit.{u + 1} T)).obj W) CK hi
    with_unfolding_all
      have h := tensor_trace_realization_with_maps C
        (Etale.derivedTensor (ModuleCat.{u + 1} A) T)
        (derivedTensor (ModuleCat.{u + 1} A) T)
        Ke (Fe.obj W) (Etale.ordinaryFiniteUnit A T) (Fe.obj S)
        (Fp.obj ((VectorIntegrationSite.comparison A (AffineSpace PUnit.{u + 1} T)).obj W)) _
        _
        ((derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
          (ModuleCat.{u + 1} A) Ke).app (Etale.ordinaryFiniteUnit A T)).hom
        pf (inverseProjection A c
          ((VectorIntegrationSite.comparison A (AffineSpace PUnit.{u + 1} T)).obj W) CK hi).symm
        ((compactSupportSiteComparison A c).inv.app ⟨_, hS⟩)
        (Fp.map (tensorPullbackComparison A (AffineSpace PUnit.{u + 1} T ↘ T) Ke W).hom)
        ((compactSupportSiteComparison A c).inv.app ⟨_, hW⟩)
        (integration A N hA T hN hT) t (Etale.derivedTensorSingleUnitIso Ke).hom
        (moduleRightUnit A T CK).hom ((adjunction A N hA T hN hT).counit.app Ke)
        a _ hsq ht
        (by with_unfolding_all exact hn)
        (by with_unfolding_all exact tensor_unit_comparison A T Ke) he
        (hpe.trans (by rfl))
        (heproj.trans (geometric_image_projection_expansion
          (ModuleCat.{u + 1} A) c W Ke hW))
    unfold projectionTensorTrace
    with_unfolding_all exact h
  · run_tac Lean.Elab.Tactic.withMainContext do
      let g ← Lean.Elab.Tactic.getMainGoal
      let h : Lean.MVarId := ⟨← g.getTag⟩
      let proof ← Lean.instantiateMVars (Lean.mkMVar h)
      let proof ← Lean.Meta.zetaReduce proof
      let proof ← normalizeCoordinateInstances proof #[
        ``VectorIntegrationSite.comparison, ``geoP1Comparison, ``tensorComparison,
        ``Etale.cartierAbelianEtale, ``Etale.cartierAbelianPro,
        ``projectionSourceObject, ``projectionTargetObject,
        ``Etale.ordinaryFinitePullback, ``Etale.ordinaryFinitePushforward]
      let proof ← transportCoordinateApplications proof
      if proof.hasSorry || proof.hasMVar then
        Lean.throwError "The comparison conversion left an unfinished proof"
      g.assign proof
      Lean.Elab.Tactic.replaceMainGoal []

private theorem compact_comparison_component
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Etale.DerivedCategoryModule A X)
    (hM : DerivedCategory.TStructure.t.plus M) :
    (fixedCompactSupportComparisonIso A c).inv.app ⟨M, hM⟩ =
      (compactSupportSiteComparison A c).inv.app ⟨M, hM⟩ := by
  have h := congrArg Iso.inv (compactSupportComparisonNormalization A c)
  exact congrArg (fun η ↦ η.app ⟨M, hM⟩) h

set_option maxHeartbeats 1000000 in
-- Specializing the finite coefficient ring requires a larger elaboration budget.
private theorem realization_at_origin
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke) :
    (fixedCompactSupportComparisonIso (Ring P)
        (affineTraceLineCompactification T)).inv.app
      ⟨etaleSource P.coefficients.l P.extension (P.level - 1) T r hA Ke,
        etaleSource_plus P.coefficients.l P.extension (P.level - 1) T r hA Ke hKe⟩ ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
      (affineTraceLineCompactification T)).map
        (sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA
          ((VectorIntegrationSite.comparison (Ring P) T).obj Ke) Ke (Iso.refl _)).hom ≫
    augmentation P.coefficients.l P.extension (P.level - 1) T r hA
      (primeUnit P T aT) P.field.k aT
        ((VectorIntegrationSite.comparison (Ring P) T).obj Ke) Ke hKe (Iso.refl _) =
    (VectorIntegrationSite.comparison (Ring P) T).map
      ((Etale.affineTraceLineLeft (Ring P) T).map (sourceCoordinates P T r hA Ke).hom ≫
        (adjunction (Ring P) (P.coefficients.l ^ (r + 1)) hA T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
          (by simpa -implicitDefEqProofs only [Nat.cast_pow] using
            (primeUnit P T aT).pow (r + 1))).counit.app Ke) := by
  let A := Ring P
  let N := P.coefficients.l ^ (r + 1)
  have hW : DerivedCategory.TStructure.t.bounded (line A N hA T) :=
    ordinaryPullback_bounded A (ProjectiveLine.affineChart T) _
      (shiftedLine_bounded A N hA (ProjectiveLine T))
  have hS := etaleSource_plus P.coefficients.l P.extension (P.level - 1) T r hA Ke hKe
  rw [etaleSource_eq, etaleCoefficient_eq] at hS
  have hN : 0 < N := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  have hT : IsUnit (N : Γ(T, ⊤)) := by
    simpa -implicitDefEqProofs only [N, Nat.cast_pow] using (primeUnit P T aT).pow (r + 1)
  have ht := integration_comparison P T r hA (primeUnit P T aT)
  have hi := AffineLinePurity.projection_isIso P.coefficients.l P.extension (P.level - 1)
    T r hA P.field.k aT (primeUnit P T aT)
    ((VectorIntegrationSite.comparison A T).obj Ke) Ke hKe (Iso.refl _)
  have h := core_realization A N hA T hN hT Ke hKe hW.1 hS
    (AffineLinePurity.integration P.coefficients.l P.extension (P.level - 1) T r hA
      (primeUnit P T aT)) ht hi
  conv_lhs =>
    arg 1
    rw [compact_comparison_component]
  conv_lhs =>
    arg 2
    arg 1
    rw [sourceComparison_refl]
  conv_rhs =>
    rw [sourceCoordinates_hom]
  conv_rhs =>
    rw [(Etale.affineTraceLineLeft (Ring P) T).map_id
      ((right (Ring P) (P.coefficients.l ^ (r + 1)) hA T).obj Ke)]
    erw [Category.id_comp ((adjunction (Ring P) (P.coefficients.l ^ (r + 1))
      hA T hN hT).counit.app Ke)]
  unfold augmentation
  with_unfolding_all exact h

set_option maxHeartbeats 1000000 in
-- The final naturality calculation specializes the derived comparison at the finite ring.
/-- The actual affine augmentation is the realization of the composite ordinary counit.
Source: current blueprint, final site-comparison paragraph of
cor-pur-affine-space-zero-section-purity.proof.md
(blueprint: lem-route-coordinate-line-augmentation-realization).

Proof: expand the standard compactification comparison into exact open extension
comparison and the specified proper direct-image mate. The open counit comparison
and projectiveComparison's trace equation identify the restricted trace with
comparison of Rq*(e_V) followed by t_q. The tensor/exchange square for the proper
mate and the open projection square identify the canonical projections, including
pullback composition. Both projections are invertible on the stated finite-Tor
input. Invert that square, tensor the trace equation and use the unit-normalized
monoidal comparison (siteTensorUnitEvaluation). This gives comparison of the
ordinary inverse-projection
trace composite. The ordinary counit tensor formula identifies it with the actual
composite counit. Naturality transports from comparison of Ke to K along eK.
The retained sourceCoordinates and sourceComparison are precisely the coordinate
maps of these squares. The fixed and canonical compactification comparisons agree
by their identical exact open map and proper counit mate; expanding their inclusion
comparisons cancels the intervening identities. All inputs to the proper mate are
bounded below by etaleSource_plus. Empty schemes and zero coefficients are included. -/
theorem coordinate_line_augmentation_realization
    (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT] [IsNoetherian T]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Ring P)) T Ke)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    (fixedCompactSupportComparisonIso (Ring P)
        (affineTraceLineCompactification T)).inv.app
      ⟨etaleSource P.coefficients.l P.extension (P.level - 1) T r hA Ke,
        etaleSource_plus P.coefficients.l P.extension (P.level - 1) T r hA Ke hKe⟩ ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
      (affineTraceLineCompactification T)).map
        (sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA
          K.obj Ke eK).hom ≫
    augmentation P.coefficients.l P.extension (P.level - 1) T r hA
      (primeUnit P T aT) P.field.k aT K.obj Ke hKe eK =
    (VectorIntegrationSite.comparison (Ring P) T).map
      ((Etale.affineTraceLineLeft (Ring P) T).map (sourceCoordinates P T r hA Ke).hom ≫
        (adjunction (Ring P) (P.coefficients.l ^ (r + 1)) hA T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
          (by simpa only [Nat.cast_pow] using (primeUnit P T aT).pow (r + 1))).counit.app Ke) ≫
      eK.hom := by
  have ho := realization_at_origin P T aT r hA Ke hKe
  have hf := sourceComparison_hom_factor P.coefficients.l P.extension (P.level - 1)
    T r hA K.obj Ke eK
  have hn := projectionTensorTrace_natural (Ring P) (affineTraceLineCompactification T)
    (coefficient P.coefficients.l P.extension (P.level - 1) T r hA) eK.hom
    (AffineLinePurity.integration P.coefficients.l P.extension (P.level - 1) T r hA
      (primeUnit P T aT))
    (AffineLinePurity.projection_isIso P.coefficients.l P.extension (P.level - 1) T r hA
      P.field.k aT (primeUnit P T aT) _ Ke hKe (Iso.refl _))
    (AffineLinePurity.projection_isIso P.coefficients.l P.extension (P.level - 1) T r hA
      P.field.k aT (primeUnit P T aT) K.obj Ke hKe eK)
  unfold augmentation at ho ⊢
  rw [hf, Functor.map_comp]
  simp -implicitDefEqProofs only [Category.assoc]
  rw [hn]
  simpa -implicitDefEqProofs only [Category.assoc] using congrArg (fun v ↦ v ≫ eK.hom) ho

end AlgebraicGeometry.ProEtale.CoordinateLine
