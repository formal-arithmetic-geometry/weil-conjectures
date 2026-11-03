/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorSupport
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceThomMap
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Logic.Small.Defs
public import Mathlib.Tactic
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorBoundaryUnit
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorClosedCompositionNormalization
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorCoefficientProjection
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorCup
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting

/-! # Binary supported cup and the last-section projection

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, projection formula sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

attribute [local irreducible] projectionMap

end AlgebraicGeometry.ProEtale.AffineZeroPurity

namespace AlgebraicGeometry.ProEtale.AffineZeroPurity

private theorem successorPiHEq {α β : Sort v} {F : α → Sort w} {G : β → Sort w}
    (h : α = β) (hFG : HEq F G) : HEq ((x : α) → F x) ((x : β) → G x) := by
  cases h
  cases hFG
  rfl

private theorem successorInferInstanceHEq {α : Sort v} (a : α) :
    HEq (@inferInstance α a) a := by
  rfl

private theorem successorFullSubcategoryObjHEq {C : Type v} [CategoryTheory.Category.{w} C]
    {P : CategoryTheory.ObjectProperty C}
    (X : C) (hX : P X) :
    HEq ((⟨X, hX⟩ : P.FullSubcategory).obj) X := by
  rfl

private def successorInstanceNormalize (e : Lean.Expr) (fuel : Nat) :
    Lean.Meta.MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e := e.consumeMData
    if e.isAppOf ``AlgebraicGeometry.Etale.cartierAbelianEtale ||
        e.isAppOf ``AlgebraicGeometry.Etale.cartierAbelianPro then
      if let some e ← Lean.Meta.withTransparency .all (Lean.Meta.unfoldDefinition? e) then
        return ← successorInstanceNormalize e fuel
    match e with
    | .letE _ _ v b _ => successorInstanceNormalize (b.instantiate1 v) fuel
    | .fvar id =>
      match (← Lean.getLCtx).get! id |>.value? (allowNondep := true) with
      | some v =>
        modifyThe Lean.Meta.State fun s ↦
          { s with zetaDeltaFVarIds := s.zetaDeltaFVarIds.insert id }
        successorInstanceNormalize v fuel
      | none => return e
    | .app f a =>
      let f ← successorInstanceNormalize f fuel
      let b := (Lean.mkApp f a).headBeta
      if b != e then successorInstanceNormalize b fuel else return e
    | _ => return e

private def successorInstanceHEq (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (a b : Lean.Expr) (fuel : Nat) : Lean.Meta.MetaM Lean.Expr := do
  let a ← Lean.instantiateMVars a
  let b ← Lean.instantiateMVars b
  if let some h := (← cache.get).get? (a, b) then return h
  let compute (_ : Unit) : Lean.Meta.MetaM Lean.Expr := do
    match fuel with
    | 0 => throwError "structural congruence fuel exhausted"
    | fuel + 1 =>
      let a ← Lean.instantiateMVars a
      let b ← Lean.instantiateMVars b
      if a == b then return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      let a ← successorInstanceNormalize a 100
      let b ← successorInstanceNormalize b 100
      if a == b then return ← Lean.Meta.mkHEqRefl a
      if a.isAppOf ``inferInstance then
        let x := a.getAppArgs.back!
        let h ← Lean.Meta.mkAppM ``successorInferInstanceHEq #[x]
        let h' ← successorInstanceHEq cache x b fuel
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      if b.isAppOf ``inferInstance then
        let x := b.getAppArgs.back!
        let h ← successorInstanceHEq cache a x fuel
        let h' ← Lean.Meta.mkAppM ``successorInferInstanceHEq #[x]
        let h' ← Lean.Meta.mkAppM ``HEq.symm #[h']
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      let project (e : Lean.Expr) : Lean.Meta.MetaM (Option (Lean.Expr × Lean.Expr)) := do
        let value? := if e.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory.obj then
          some e.getAppArgs.back!
        else match e with
          | .proj n 0 x =>
            if n == ``CategoryTheory.ObjectProperty.FullSubcategory then some x else none
          | _ => none
        let some value := value? | return none
        let value ← successorInstanceNormalize value 100
        unless value.isAppOf ``CategoryTheory.ObjectProperty.FullSubcategory.mk do return none
        let args := value.getAppArgs
        let x := args[args.size - 2]!
        let h ← Lean.Meta.mkAppM ``successorFullSubcategoryObjHEq #[x, args.back!]
        return some (x, h)
      if let some (x, h) ← project a then
        let h' ← successorInstanceHEq cache x b fuel
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      if let some (x, h') ← project b then
        let h ← successorInstanceHEq cache a x fuel
        let h' ← Lean.Meta.mkAppM ``HEq.symm #[h']
        return ← Lean.Meta.mkAppM ``HEq.trans #[h, h']
      match a, b with
      | .lam _ ta _ _, .lam _ tb _ _ =>
        let hdom ← Lean.Meta.mkAppM ``eq_of_heq #[← successorInstanceHEq cache ta tb fuel]
        let g ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkAppM ``HEq #[a, b])
        let gs ← g.mvarId!.apply
          (← Lean.Meta.mkConstWithFreshMVarLevels ``Function.hfunext)
        unless gs.length == 2 do throwError "unexpected hfunext goals"
        gs[0]!.assign hdom
        let (_, g1) ← gs[1]!.intro1
        let (_, g2) ← g1.intro1
        let (h, g3) ← g2.intro1
        for c in ← g3.cases h do
          c.mvarId.withContext do
            let t ← c.mvarId.getType
            let args := t.getAppArgs
            unless args.size == 4 do throwError "expected HEq after hfunext"
            c.mvarId.assign (← successorInstanceHEq cache args[1]! args[3]! fuel)
        return ← Lean.instantiateMVars g
      | .forallE n ta ab bi, .forallE n' tb bb bi' =>
        let hdom ← Lean.Meta.mkAppM ``eq_of_heq #[← successorInstanceHEq cache ta tb fuel]
        let hf ← successorInstanceHEq cache (.lam n ta ab bi) (.lam n' tb bb bi') fuel
        return ← Lean.Meta.mkAppM ``successorPiHEq #[hdom, hf]
      | _, _ => pure ()
      let af := a.getAppFn
      let bf := b.getAppFn
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      let sameHead ← match af, bf with
        | .const n _, .const m _ =>
          if n == m then Lean.Meta.isDefEq af bf else pure false
        | _, _ => pure (af == bf)
      if sameHead && aa.size == ba.size && !aa.isEmpty then
        let ct ← Lean.Meta.mkHCongrWithArity af aa.size
        let mut args := #[]
        for i in [:aa.size] do
          let h ← successorInstanceHEq cache aa[i]! ba[i]! fuel
          let h ← match ct.argKinds[i]! with
            | .eq => Lean.Meta.mkAppM ``eq_of_heq #[h]
            | .heq => pure h
            | _ => throwError "unexpected congruence argument kind"
          args := args ++ #[aa[i]!, ba[i]!, h]
        let h := Lean.mkAppN ct.proof args
        let h ← if (← Lean.Meta.inferType h).isEq then
          Lean.Meta.mkAppM ``heq_of_eq #[h]
        else pure h
        return h
      throwError "cannot structurally compare\n{a}\nWITH\n{b}"
  let h ← compute ()
  let h ← Lean.instantiateMVars h
  let h ← if a == b then pure h else do
    let h ← Lean.Meta.mkAuxTheorem (← Lean.Meta.mkAppM ``HEq #[a, b]) h
      (zetaDelta := true) (kind? := `_successor_congr)
    pure h
  cache.modify (fun c ↦ c.insert (a, b) h)
  return h

private theorem projection_naturality_generic
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    {K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (α : K ⟶ L) :
    ((derivedTensor A X).obj ((rightDerivedLowerShriek A s).obj M)).map α ≫
      ((projectionMap A s).app M).app L =
      ((projectionMap A s).app M).app K ≫ (rightDerivedLowerShriek A s).map
        (((derivedTensor A Y).obj M).map ((upperStar A s).leftDerivedFunctor.map α)) := by
  exact ((projectionMap A s).app M).naturality α

private theorem sectionProjectionComponent_eq
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s] (q : X ⟶ Y)
    (M K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :
    sectionProjectionComponent A s q M K =
      (((projectionMap (ModuleCat.{u + 1} A) s).app M).app
        ((AffineSpacePurity.inverseImage A q).obj K)) := by
  have h := sectionProjectionComponent.eq_def A s q M K
  run_tac Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let decls := (← Lean.getLCtx).decls.toList.filterMap id
    let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == `h) |
      throwError "missing generated equation"
    let h := d.toExpr
    let cache ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let e ← successorInstanceHEq cache (← g.getType) (← Lean.Meta.inferType h) 1000
    let e ← Lean.Meta.mkAppM ``eq_of_heq #[e]
    g.assign (← Lean.Meta.mkAppM ``Eq.mpr #[e, h])

private theorem sectionProjectionComponent_naturality
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s]
    (q : X ⟶ Y)
    (M K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (α : K ⟶ L) :
    ((AffineSpacePurity.tensor A X).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).obj M)).map
          ((AffineSpacePurity.inverseImage A q).map α) ≫
      sectionProjectionComponent A s q M L =
      sectionProjectionComponent A s q M K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).map
          (((AffineSpacePurity.tensor A Y).obj M).map
            ((AffineSpacePurity.inverseImage A s).map
              ((AffineSpacePurity.inverseImage A q).map α))) := by
  rw [sectionProjectionComponent_eq, sectionProjectionComponent_eq]
  exact projection_naturality_generic (ModuleCat.{u + 1} A) s M
    ((AffineSpacePurity.inverseImage A q).map α)

private theorem tensor_section_unit_naturality {C : Type v} [Category.{w} C]
    [MonoidalCategory C] (F : C ⥤ C) (E : F ≅ 𝟭 C) {M K L : C}
    (e : M ≅ 𝟙_ C) (α : K ⟶ L) :
    (𝟙 M ⊗ₘ F.map α) ≫ (e.hom ⊗ₘ E.hom.app L) ≫ (λ_ L).hom =
      (e.hom ⊗ₘ E.hom.app K) ≫ (λ_ K).hom ≫ α := by
  have hn := E.hom.naturality α
  change F.map α ≫ E.hom.app L = E.hom.app K ≫ α at hn
  calc
    _ = (e.hom ⊗ₘ F.map α ≫ E.hom.app L) ≫ (λ_ L).hom := by
      rw [tensorHom_comp_tensorHom_assoc, Category.id_comp]
    _ = (e.hom ⊗ₘ E.hom.app K ≫ α) ≫ (λ_ L).hom := by rw [hn]
    _ = (e.hom ⊗ₘ E.hom.app K) ≫ (𝟙_ C ◁ α) ≫ (λ_ L).hom := by
      rw [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id]
    _ = _ := by
      rw [leftUnitor_naturality]
      simp only [Functor.id_obj]

/-- The section endpoint identification is natural in its coefficient input.
Source: naturality of the projection formula in the zero-section product.
(blueprint: lem-pur-coordinate-successor-cup-projection).
Proof: the pullback compositor and section equation form a natural isomorphism
from the double inverse image to identity. Its naturality moves the input map
through the second tensor factor. Tensor bifunctoriality moves it past the
coefficient-unit comparison, and naturality of the left unitor finishes. -/
theorem sectionTensorRaw_naturality (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) (q : X ⟶ Y) (h : s ≫ q = 𝟙 Y)
    (M K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M ≅ 𝟙_ _) (α : K ⟶ L) :
    ((tensor A Y).obj M).map
        ((inverseImage A s).map ((inverseImage A q).map α)) ≫
      (sectionTensorRaw A s q h M L e).hom =
        (sectionTensorRaw A s q h M K e).hom ≫ α := by
  let F := inverseImage A q ⋙ inverseImage A s
  let E : F ≅ 𝟭 _ := (inverseImageComp A s q).symm ≪≫
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) h ≪≫ inverseImageId A Y
  have hn := tensor_section_unit_naturality F E e α
  unfold sectionTensorRaw AffineSpacePurity.tensorIso tensorUnitLeftIso
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    eqToIso_refl, Iso.refl_hom, Category.id_comp, AffineSpacePurity.tensor, derivedTensor,
    curriedTensor_obj_map, curriedTensor_map_app, MonoidalCategory.tensorHom_def, Category.assoc,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, id_whiskerRight,
    Category.id_comp, F, E] using hn

private theorem map_square_postcompose {C D : Type v} [Category.{w} C]
    [Category.{w} D] (F : C ⥤ D) {M N K L : C} {X Y : D}
    (f : X ⟶ Y) (p : X ⟶ F.obj M) (q : Y ⟶ F.obj N)
    (g : M ⟶ N) (eM : M ⟶ K) (eN : N ⟶ L) (a : K ⟶ L)
    (hp : f ≫ q = p ≫ F.map g) (he : g ≫ eN = eM ≫ a) :
    f ≫ (q ≫ F.map eN) = (p ≫ F.map eM) ≫ F.map a := by
  rw [← Category.assoc, hp, Category.assoc, ← F.map_comp, he, F.map_comp,
    Category.assoc]

private theorem sectionProjectionRaw_naturality
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s]
    (q : X ⟶ Y) (h : s ≫ q = 𝟙 Y)
    (M K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M ≅ 𝟙_ _) (α : K ⟶ L) :
    ((tensor A X).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).obj M)).map
          ((inverseImage A q).map α) ≫ sectionProjectionRaw A s q h M L e =
      sectionProjectionRaw A s q h M K e ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).map α := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) s
  have hp := sectionProjectionComponent_naturality A s q M K L α
  have ht := sectionTensorRaw_naturality A s q h M K L e α
  unfold sectionProjectionRaw projectionPostcompose
  simp only [Functor.mapIso_hom]
  exact map_square_postcompose F _ _ _ _ _ _ _ hp ht

/-- The chosen section arrow satisfies its precise projection equation.
Source: the inverse projection definition in the affine-space zero-section proof.
(blueprint: lem-pur-coordinate-successor-cup-projection).
Proof: project the characterizing equality of the uniquely chosen section arrow.
Convert its heterogeneous equality to equality; the endpoints are the specified
section projection and tensor target normalization. -/
theorem coordinate_sectionArrow_projection (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    sectionProjection P n B r ≫ sectionArrow P n B aB r =
      tensorArrow (tensor (setting P n).Coefficient (iteratedAffineLine B (r + 1)))
        (lastProduct P n B aB r)
        ((inverseImage (setting P n).Coefficient (lastProjection B r)).obj
          (target P n (iteratedAffineLine B r) r)) (sectionTargetIso P n B aB r) := by
  unfold sectionArrow
  exact eq_of_heq (sectionArrow_existsUnique P n B aB r).exists.choose_spec

-- Normalize the selected-site Hom presentation before using ordinary functor laws.

private theorem tensor_boundary_factorization {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C]
    {A B K M V T₁ L T : C}
    (s : A ⟶ K) (b : B ⟶ M) (ℓ : M ⟶ T₁) (e : T₁ ≅ L)
    (α : K ⟶ V) (f : V ≅ T) (boundary : B ⟶ L)
    (hb : b ≫ ℓ ≫ e.hom = boundary) :
    (s ≫ α ≫ f.hom) ⊗ₘ boundary =
      (s ⊗ₘ b) ≫ (β_ K M).hom ≫ (M ◁ α) ≫
        (ℓ ▷ V) ≫ (e.hom ⊗ₘ f.hom) ≫ (β_ L T).hom := by
  rw [← hb]
  rw [← id_tensorHom, ← tensorHom_id]
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]
  rw [← BraidedCategory.braiding_naturality_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]
  simp only [tensorHom_comp_tensorHom_assoc]
  rw [SymmetricCategory.symmetry, Category.comp_id]

private theorem projection_cup_paste {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {M N K : C} {X U V Z : D}
    (τ : X ⟶ U) (a : U ⟶ V) (pM : U ⟶ F.obj M) (pN : V ⟶ F.obj N)
    (t : V ⟶ Z) (z : F.obj N ⟶ Z) (c : X ⟶ F.obj K)
    (b : K ⟶ M) (α : M ⟶ N)
    (hn : a ≫ pN = pM ≫ F.map α)
    (hc : τ ≫ pM = c ≫ F.map b) (ht : pN ≫ z = t) :
    τ ≫ a ≫ t = c ≫ F.map (b ≫ α) ≫ z := by
  rw [← ht, ← Category.assoc a pN z, hn, Category.assoc pM (F.map α) z,
    ← Category.assoc τ pM (F.map α ≫ z), hc]
  simp only [Functor.map_comp, Category.assoc]

private theorem successorCup_tensor_expansion (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (α : classSource P n B (r + 1) (successorTailList r) ⟶
      target P n (iteratedAffineLine B (r + 1)) r) :
    let := zero_exact P n B aB (r + 1)
    (closedSingleIso (setting P n).Coefficient (zero B (r + 1))
      ((setting P n).constant B)).hom ≫ successorCup P n B aB r α =
    successorBinaryCoefficient P n B aB r ≫
      ((eqToHom (classSource_eq P n B (r + 1) (successorTailList r)).symm ≫ α) ⊗ₘ
        boundary P n B aB (r + 1) 0) ≫
      eqToHom (target_succ P n (iteratedAffineLine B (r + 1)) r) := by
  let := zero_exact P n B aB (r + 1)
  unfold successorCup successorBinaryCoefficient coordinateSupportedCompose
    coordinateProductStart zeroCupTensor
  dsimp only [successorTailMap]
  simp only [Category.assoc]

private theorem fixed_tensorIso_hom (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (e : M ≅ M') (f : N ≅ N') :
    (tensorIso A X e f).hom = e.hom ⊗ₘ f.hom := by rfl

private theorem fixed_tensorSwap_hom (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    let := DerivedCategory.braidedCategory'
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (tensorSwap A X M N).hom = (β_ M N).hom := by
  let := DerivedCategory.braidedCategory'
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
  unfold tensorSwap
  change 𝟙 _ ≫ (β_ M N).hom ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

private theorem fixed_tensor_obj_map (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    (M K L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (f : K ⟶ L) : ((tensor A X).obj M).map f = M ◁ f := by rfl

private theorem fixed_tensorArrow_reverse (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u})
    {M M' V K K' : DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (ℓ : M ⟶ V) (e : V ≅ M') (f : K ≅ K') :
    let := DerivedCategory.braidedCategory'
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    tensorArrow (tensor A X) ℓ K (reverseTensorIso A X e f) =
      ℓ ▷ K ≫ (e.hom ⊗ₘ f.hom) ≫ (β_ M' K').hom := by
  let := DerivedCategory.braidedCategory'
    (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
  unfold tensorArrow reverseTensorIso
  rw [Iso.trans_hom, fixed_tensorIso_hom, fixed_tensorSwap_hom]
  rfl

private theorem sectionTargetIso_eq (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    sectionTargetIso P n B aB r =
      reverseTensorIso (setting P n).Coefficient (iteratedAffineLine B (r + 1))
        (oneTargetIso P n (iteratedAffineLine B (r + 1)))
        (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r) := by
  unfold sectionTargetIso
  exact eq_of_heq (sectionTargetIso_existsUnique P n B aB r).exists.choose_spec

private theorem seven_factor_grouping {C : Type u} [Category.{v} C]
    {A B C₁ D E F G H : C} (a : A ⟶ B) (b : B ⟶ C₁) (c : C₁ ⟶ D)
    (d : D ⟶ E) (e : E ⟶ F) (f : F ⟶ G) (g : G ⟶ H) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f ≫ g = (a ≫ b ≫ c) ≫ d ≫ (e ≫ f ≫ g) := by
  simp only [Category.assoc]

private theorem successorCup_sectionTensor_factorization
    (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (α : (cupSingle (setting P n) (iteratedAffineLine B r)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B r) r)
    (hb : successorLastCoefficient P n B aB r ≫ lastProduct P n B aB r ≫
        (oneTargetIso P n (iteratedAffineLine B (r + 1))).hom =
          boundary P n B aB (r + 1) 0) :
    let := zero_exact P n B aB (r + 1)
    (closedSingleIso (setting P n).Coefficient (zero B (r + 1))
      ((setting P n).constant B)).hom ≫
        successorCup P n B aB r
          ((successorTailSourcePullback P n B r).inv ≫
            (inverseImage (setting P n).Coefficient (lastProjection B r)).map α ≫
              (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r).hom) =
    successorCoefficientTensor P n B aB r ≫
      ((tensor (setting P n).Coefficient (iteratedAffineLine B (r + 1))).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).obj (unit P n (iteratedAffineLine B r)))).map
            ((inverseImage (setting P n).Coefficient (lastProjection B r)).map α) ≫
      tensorArrow (tensor (setting P n).Coefficient (iteratedAffineLine B (r + 1)))
        (lastProduct P n B aB r)
        ((inverseImage (setting P n).Coefficient (lastProjection B r)).obj
          (target P n (iteratedAffineLine B r) r)) (sectionTargetIso P n B aB r) := by
  let := zero_exact P n B aB (r + 1)
  dsimp only
  let := DerivedCategory.symmetricCategory'
    (Sheaf (Scheme.ProEt.topology (iteratedAffineLine B (r + 1)))
      (ModuleCat.{u + 1} (setting P n).Coefficient))
  erw [successorCup_tensor_expansion P n B aB r]
  erw [sectionTargetIso_eq]
  erw [fixed_tensorArrow_reverse]
  unfold successorCoefficientTensor
  erw [fixed_tensorSwap_hom, fixed_tensor_obj_map]
  have hcast : eqToHom
      (target_succ P n (iteratedAffineLine B (r + 1)) r) =
        𝟙 (target P n (iteratedAffineLine B (r + 1)) (r + 1)) := by rfl
  erw [hcast, Category.comp_id]
  have ht := tensor_boundary_factorization
    (C := D P n (iteratedAffineLine B (r + 1)))
    (eqToHom (classSource_eq P n B (r + 1) (successorTailList r)).symm ≫
      (successorTailSourcePullback P n B r).inv)
    (successorLastCoefficient P n B aB r) (lastProduct P n B aB r)
    (oneTargetIso P n (iteratedAffineLine B (r + 1)))
    ((inverseImage (setting P n).Coefficient (lastProjection B r)).map α)
    (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r) _ hb
  have h := congrArg (fun z ↦ successorBinaryCoefficient P n B aB r ≫ z) ht
  erw [Category.assoc
    (eqToHom (classSource_eq P n B (r + 1) (successorTailList r)).symm)
    (successorTailSourcePullback P n B r).inv] at h
  exact h.trans (seven_factor_grouping
    (C := D P n (iteratedAffineLine B (r + 1))) _ _ _ _ _ _ _)

private theorem projection_closure (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (α : (cupSingle (setting P n) (iteratedAffineLine B r)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B r) r)
    (hb : successorLastCoefficient P n B aB r ≫ lastProduct P n B aB r ≫
        (oneTargetIso P n (iteratedAffineLine B (r + 1))).hom =
          boundary P n B aB (r + 1) 0)
    (hc : letI : IsNoetherianRing (setting P n).Coefficient :=
        isNoetherian_of_finite (setting P n).Coefficient (setting P n).Coefficient
      let := zero_exact P n B aB r
      successorCoefficientTensor P n B aB r ≫
        sectionProjectionRaw (setting P n).Coefficient (lastSection B r) (lastProjection B r)
          (Scheme.Hom.toIteratedAffineLine_comp_over (𝟙 _) (fun _ ↦ 0))
          (unit P n (iteratedAffineLine B r))
          ((cupSingle (setting P n) (iteratedAffineLine B r)).obj
            ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).obj
              ((setting P n).constant B)))
          (coefficientUnitIso P n (iteratedAffineLine B r)) =
        (coordinateComposition P n B r).hom ≫
          (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
            (lastSection B r)).map
            (closedSingleIso (setting P n).Coefficient (zero B r)
              ((setting P n).constant B)).hom)
 :
    let := zero_exact P n B aB r
    let := zero_exact P n B aB (r + 1)
    (closedSingleIso (setting P n).Coefficient (zero B (r + 1))
      ((setting P n).constant B)).hom ≫
        successorCup P n B aB r
          ((successorTailSourcePullback P n B r).inv ≫
            (inverseImage (setting P n).Coefficient (lastProjection B r)).map α ≫
              (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r).hom) =
      (coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map
            ((closedSingleIso (setting P n).Coefficient (zero B r)
              ((setting P n).constant B)).hom ≫ α) ≫ sectionArrow P n B aB r := by
  let : IsNoetherianRing (setting P n).Coefficient :=
    isNoetherian_of_finite (setting P n).Coefficient (setting P n).Coefficient
  let := zero_exact P n B aB r
  let := zero_exact P n B aB (r + 1)
  dsimp only
  erw [successorCup_sectionTensor_factorization P n B aB r α hb]
  let A := (setting P n).Coefficient
  let Y := iteratedAffineLine B r
  let X := iteratedAffineLine B (r + 1)
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (lastSection B r)
  let M := unit P n Y
  let K := (cupSingle (setting P n) Y).obj
    ((lowerStar (ModuleCat.{u + 1} A) (zero B r)).obj ((setting P n).constant B))
  let W := target P n Y r
  let q := lastProjection B r
  let s := lastSection B r
  let h : s ≫ q = 𝟙 Y :=
    Scheme.Hom.toIteratedAffineLine_comp_over (𝟙 Y) (fun _ : Fin 1 ↦ 0)
  let e := coefficientUnitIso P n Y
  have hn := sectionProjectionRaw_naturality A s q h M K W e α
  have ht := coordinate_sectionArrow_projection P n B aB r
  have he : sectionProjection P n B r = sectionProjectionRaw A s q h M W e := by
    unfold sectionProjection
    rfl
  erw [he] at ht
  exact projection_cup_paste F (successorCoefficientTensor P n B aB r)
    (((tensor A X).obj (F.obj M)).map ((inverseImage A q).map α))
    (sectionProjectionRaw A s q h M K e) (sectionProjectionRaw A s q h M W e)
    _ (sectionArrow P n B aB r) (coordinateComposition P n B r).hom
    (closedSingleIso A (zero B r) ((setting P n).constant B)).hom α hn hc ht

/-- Cupping an arbitrary supported input with the last boundary is the section
arrow after direct image of that input. No coordinate product is assumed for α.
Source: the coefficient multiplication and projection formula sentence of the
current affine-space zero-section proof.
(blueprint: lem-pur-coordinate-successor-cup-projection).

Proof: the proved single-cup unit law identifies the singleton last product with
the newest Cartier boundary. Expand the binary cup into its explicit coefficient
part. Tensor bifunctoriality and the two prescribed symmetries factor this cup
through successorCoefficientTensor, inverse image of α and the section tensor
arrow. The fixed coefficient-projection comparison and the separate ordinary
closed-composition normalization identify the coefficient projection with
coordinateComposition followed by direct image of closedSingleIso for the old
zero section. Projection naturality moves α across that square. Finally paste
this square with the defining projection equation of the actual sectionArrow.
Functoriality combines the old closed-single map with α, giving the displayed
equation. The proof retains the specified symmetry and every canonical unit;
it neither identifies α with a coordinate product nor uses a recurrence for it. -/
theorem coordinate_successor_cup_projection (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ)
    (α : (cupSingle (setting P n) (iteratedAffineLine B r)).obj
      ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B r)).obj
        ((setting P n).constant B)) ⟶ target P n (iteratedAffineLine B r) r) :
    let := zero_exact P n B aB r
    let := zero_exact P n B aB (r + 1)
    (closedSingleIso (setting P n).Coefficient (zero B (r + 1))
      ((setting P n).constant B)).hom ≫
        successorCup P n B aB r
          ((successorTailSourcePullback P n B r).inv ≫
            (inverseImage (setting P n).Coefficient (lastProjection B r)).map α ≫
              (targetPullbackIso P n (lastProjection B r) (towerBase aB r) r).hom) =
      (coordinateComposition P n B r).hom ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (lastSection B r)).map
            ((closedSingleIso (setting P n).Coefficient (zero B r)
              ((setting P n).constant B)).hom ≫ α) ≫ sectionArrow P n B aB r := by
  let := zero_exact P n B aB r
  let := zero_exact P n B aB (r + 1)
  exact projection_closure P n B aB r α
    (coordinate_successor_boundary_unit P n B aB r)
    ((coordinate_successor_coefficient_projection P n B aB r).trans
      (coordinate_successor_closed_composition_normalization P n B aB r).symm)

end AlgebraicGeometry.ProEtale.AffineZeroPurity
