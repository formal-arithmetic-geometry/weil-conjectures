/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarMonoidalRepresentative
import WeilConjectures.CategoryTheory.Normalized.NormalizedScalarUnitAdjunction
import Mathlib.Lean.Meta.CongrTheorems
import Mathlib.Algebra.Ring.Ext
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientUnitCoherence
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps

/-! # The scalar unit in adjoint single-complex coordinates

Source: finite reduction of purity, Step 2; Stacks 07A4 and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] finiteTensorAdjunction finiteTensorCore
  Functor.leftAdjoint Adjunction.ofIsRightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

universe v w

attribute [local irreducible] Functor.mapDerivedCategory
  _root_.DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

private theorem unit_from_representatives
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.Monoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D) (h : S.CoreMonoidal)
    (r : _root_.DerivedCategory.Q ⋙ S ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (ht : ∀ X Y : CochainComplex C ℤ,
      (h.μIso (_root_.DerivedCategory.Q.obj X) (_root_.DerivedCategory.Q.obj Y)).inv ≫
          (r.app X ⊗ₘ r.app Y) ≫ Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
            ((F.mapHomologicalComplex (.up ℤ)).obj X)
            ((F.mapHomologicalComplex (.up ℤ)).obj Y) =
        S.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q X Y) ≫ r.app (X ⊗ Y) ≫
          _root_.DerivedCategory.Q.map
            (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app X).app Y))
    (hr : ∀ X, (HomologicalComplex.quasiIso C (.up ℤ)).kFlat X → IsIso (r.app X)) :
    Etale.ExceptionalCoefficients.UnitNormalizationAux F S r.app h.εIso.symm := by
  let := h.toMonoidal
  let := hr (𝟙_ _) (HomologicalComplex.quasiIso C (.up ℤ)).kFlat.prop_unit
  obtain ⟨e, he, _⟩ := Etale.ExceptionalCoefficients.unitNormalizationAux_existsUnique
    F S r.app
  let δ := (Functor.Monoidal.μNatIso S).symm
  have hu := Etale.ExceptionalCoefficients.normalized_right_unit F S r δ e ht he hr
    (𝟙_ _)
  have hunit : e.hom = h.εIso.inv := by
    have hn := Functor.OplaxMonoidal.right_unitality_hom S (𝟙_ _)
    change (h.μIso _ _).inv ≫ (S.obj (𝟙_ _) ◁ e.hom) ≫ _ = _ at hu
    change (h.μIso _ _).inv ≫ (S.obj (𝟙_ _) ◁ h.εIso.inv) ≫ _ = _ at hn
    have hw := (cancel_epi (h.μIso _ _).inv).1 (hu.trans hn.symm)
    have hw' := (cancel_mono (ρ_ (S.obj (𝟙_ _))).hom).1 hw
    have hw'' : (𝟙_ _ : _root_.DerivedCategory D) ◁ e.hom =
        (𝟙_ _ : _root_.DerivedCategory D) ◁ h.εIso.inv := by
      apply (cancel_epi (h.εIso.inv ▷ S.obj (𝟙_ _))).1
      rw [← whisker_exchange, ← whisker_exchange, hw']
    have hh := congrArg (fun f ↦
      (λ_ (S.obj (𝟙_ _))).inv ≫ f ≫ (λ_ (𝟙_ (_root_.DerivedCategory D))).hom) hw''
    simpa only [leftUnitor_naturality, Iso.inv_hom_id_assoc] using hh
  have hi : e = h.εIso.symm := Iso.ext hunit
  simpa only [hi] using he

private theorem coefficient_ring_eq (P : PurityFiniteSetting.{u}) :
    P.coefficientCommRing = (ULift.commRing : CommRing (ULift.{u + 1} P.Ring)) := by
  apply CommRing.ext <;> rfl

-- Cache repeated instance equalities while comparing the fixed scalar coordinates.
private meta def scalarHead (fuel : Nat) (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e := e.consumeMData
    let names := [``finiteTensorReduction, ``Coefficient,
      ``ProEtale.SupportedEtaleTensorOrigin.fixedScalar,
      ``ProEtale.SupportedEtaleTensorOrigin.proFixedScalar,
      ``ProEtale.SupportedEtaleTensorOrigin.fixedRestriction,
      ``ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction,
      ``ProEtale.pbcFixedScalarExtension, ``sfFixedRestriction,
      ``Sheaf.restrictScalars, ``Sheaf.derivedRestrictScalars]
    if names.any e.getAppFn.isConstOf then
      if let some e' ← Lean.Meta.unfoldDefinition? e then
        return ← scalarHead fuel e'
    match e with
    | .letE .. => return ← scalarHead fuel (← Lean.Meta.whnf e)
    | _ =>
      if e.getAppFn.isConstOf ``CategoryTheory.Functor.obj then
        return ← Lean.Meta.withTransparency .reducible (Lean.Meta.whnf e)
      return e

private meta def scalarCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr))
    (fuel : Nat) (g : Lean.MVarId) : Lean.MetaM Unit := do
  match fuel with
  | 0 => throwError "coordinate congruence recursion limit"
  | fuel + 1 =>
    let g ← g.cleanup
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
      let a ← scalarHead 20 a
      let b ← scalarHead 20 b
      if a == b then
        if t.isHEq then g.hrefl else g.refl
      else if a.getAppFn.isConstOf ``coefficientCommRing then
        let h ← Lean.Meta.mkAppM ``coefficient_ring_eq #[a.getAppArgs[0]!]
        let h ← if t.isHEq then Lean.Meta.mkAppM ``heq_of_eq #[h] else pure h
        let gs ← g.apply h { synthAssignedInstances := false }
        for g in gs do scalarCongr cache fuel g
      else if b.getAppFn.isConstOf ``coefficientCommRing then
        let h ← Lean.Meta.mkAppM ``coefficient_ring_eq #[b.getAppArgs[0]!]
        let h ← Lean.Meta.mkAppM ``Eq.symm #[h]
        let h ← if t.isHEq then Lean.Meta.mkAppM ``heq_of_eq #[h] else pure h
        let gs ← g.apply h { synthAssignedInstances := false }
        for g in gs do scalarCongr cache fuel g
      else if ← g.proofIrrelHeq then pure ()
      else if t.isEq then
        let gs ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``eq_of_heq)
          { synthAssignedInstances := false }
        for g in gs do scalarCongr cache fuel g
      else if a.getAppFn == b.getAppFn &&
          a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
        let f := a.getAppFn
        let info ← Lean.Meta.getFunInfoNArgs f a.getAppNumArgs
        let fixed := a.getAppArgs.zipWith (· == ·) b.getAppArgs
        let c ← Lean.Meta.mkRichHCongr (← Lean.Meta.inferType f) info
          (fixedFun := true) (fixedParams := fixed) (forceHEq := t.isHEq)
        let gs ← g.apply (c.proof.beta #[f]) { synthAssignedInstances := false }
        for g in gs do scalarCongr cache fuel g
      else
        if t.isHEq then g.hrefl else g.refl
      let pf ← Lean.instantiateMVars (Lean.mkMVar g)
      cache.modify (·.insert t pf)

private theorem transpose_of_unit_square
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (a : F ⊣ G)
    {X U : C} {Y V : D} (u : X ≅ U) (v : Y ≅ V)
    (e : F.obj U ⟶ V) (j : X ⟶ G.obj Y)
    (h : F.map u.hom ≫ e ≫ v.inv = (a.homEquiv _ _).symm j) :
    u.hom ≫ a.homEquiv _ _ e = j ≫ G.map v.hom := by
  have h' := congrArg (a.homEquiv _ _) h
  rw [a.homEquiv_naturality_left, a.homEquiv_naturality_right,
    Equiv.apply_symm_apply] at h'
  have hh := congrArg (fun f ↦ f ≫ G.map v.hom) h'
  simpa only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id] using hh

private theorem core_eq_model (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) :
    P.finiteTensorCore m hm hmn T =
      finiteScalarMonoidalModel
        (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T := by
  apply (P.existsUnique_finiteTensorCore m hm hmn T).unique
  · unfold finiteTensorCore
    exact (P.existsUnique_finiteTensorCore m hm hmn T).choose_spec.1
  · exact fun C D _ _ ↦ finiteScalarMonoidalModel_representative
      (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T C D

set_option maxHeartbeats 1000000 in
-- Comparing the fixed scalar coordinates traverses several derived-category instances.
/-- The scalar core's unit inverse has the ordinary coefficient-unit transpose.
Source: finite reduction of purity, Step 2; Stacks 07A4 and 06YY.
(blueprint: lem-pur-finite-tensor-scalar-unit-transpose).
Proof: identify the core with the native scalar monoidal model using uniqueness
of its representative tensor formula. Its unit is the localized ordinary scalar
unit, transported through uniqueness of left adjoints. The ordinary scalar
adjunction sends this unit to the lax unit of restriction. Apply the exact-single
adjunction formula and the single/unit comparisons. Naturality of those comparisons
and cancellation of the adjoint-uniqueness isomorphisms give the equation. No root,
line, coefficient flatness or nonempty-base assumption occurs in this calculation. -/
theorem finiteTensorScalarUnit_transpose (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    (_root_.DerivedCategory.singleFunctorObjUnitIso
        (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))).hom ≫
      (P.finiteTensorAdjunction m hm hmn T).homEquiv _ _
        (P.finiteTensorCore m hm hmn T).εIso.inv =
    (_root_.DerivedCategory.singleFunctor.{u + 1} _ 0).map
        (Functor.LaxMonoidal.ε
          (sfFixedRestriction.{u, u + 1, u + 1} T (P.finiteReductionRingHom m hm hmn))) ≫
      (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
        (sfFixedRestriction.{u, u + 1, u + 1} T
          (P.finiteReductionRingHom m hm hmn)) 0).inv.app (𝟙_ _) ≫
      (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
        (P.finiteReductionRingHom m hm hmn) T).map
          (_root_.DerivedCategory.singleFunctorObjUnitIso
            (Sheaf (ProEt.topology T)
              (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient))).hom := by
  rw [core_eq_model]
  unfold finiteTensorAdjunction
  let φ := (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
  let F := ProEtale.sheafExtendScalars φ T
  let U := sfFixedRestriction.{u, u + 1, u + 1} T (P.finiteReductionRingHom m hm hmn)
  let a : F ⊣ U := ProEtale.sheafExtendScalarsAdjunction φ T
  let S := ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T
  let ad := Adjunction.ofIsRightAdjoint
    (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)
  let h := finiteScalarMonoidalModel φ T
  let r := Etale.ExceptionalCoefficients.adjointRepresentative
    _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) (U.mapHomologicalComplex (.up ℤ)) S
    (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
      (P.finiteReductionRingHom m hm hmn) T) ad (a.mapHomologicalComplex (.up ℤ))
    U.mapDerivedCategoryFactors.symm
  have hr : r.app = ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative
      φ T := by
    funext X
    unfold ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative
    rw [← Etale.ExceptionalCoefficients.mapComplex_unit_formula]
    rfl
  have ht : ∀ X Y, (h.μIso (_root_.DerivedCategory.Q.obj X)
      (_root_.DerivedCategory.Q.obj Y)).inv ≫ (r.app X ⊗ₘ r.app Y) ≫
        Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj X)
          ((F.mapHomologicalComplex (.up ℤ)).obj Y) =
      S.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q X Y) ≫ r.app (X ⊗ Y) ≫
        _root_.DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app X).app Y) := by
    intro X Y
    rw [congrFun hr X, congrFun hr Y, congrFun hr (X ⊗ Y)]
    have ht := finiteScalarMonoidalModel_representative φ T X Y
    unfold TensorRepresentativeData.source at ht
    unfold finiteScalarTensorData at ht
    simpa only [cochainLocalizationTensor, finiteTensorCochainComparison] using ht.symm
  have hi : ∀ X, (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat X →
      IsIso (r.app X) := by
    intro X hX
    rw [congrFun hr X]
    exact finiteScalarRepresentative_isIso φ T X hX
  have hu := unit_from_representatives F S h r ht hi
  have hm : a.homEquiv _ _ (Functor.OplaxMonoidal.η F) =
      Functor.LaxMonoidal.ε U := by
    exact (a.homEquiv _ _).apply_symm_apply _
  have hs := SheafExactDegreeZero.normalizedUnit_singleAdjunction F U a S ad r.app
    h.εIso.symm hu rfl hm
  unfold SheafExactDegreeZero.adjointInsertion at hs
  have hf := transpose_of_unit_square S U.mapDerivedCategory ad
    (_root_.DerivedCategory.singleFunctorObjUnitIso _)
    (_root_.DerivedCategory.singleFunctorObjUnitIso _) h.εIso.inv _ hs
  dsimp (config := { instances := true }) only
    [U, h, ad, S, φ, Coefficient, inferInstance, finiteTensorReduction,
    ProEtale.SupportedEtaleTensorOrigin.fixedScalar,
    ProEtale.SupportedEtaleTensorOrigin.proFixedScalar, ProEtale.pbcFixedScalarExtension,
    ProEtale.SupportedEtaleTensorOrigin.fixedRestriction,
    ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction,
    ProEtale.SupportedEtaleTensorOrigin.liftedHom,
    sfFixedRestriction, Sheaf.derivedRestrictScalars, Sheaf.restrictScalars] at hf ⊢
  simp only [Category.assoc] at hf ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    let hf ← Lean.Elab.Term.elabTerm (Lean.mkIdent `hf) none
    let goal ← Lean.Elab.Tactic.getMainGoal
    let source ← Lean.Meta.inferType hf
    let target ← goal.getType
    let equality ← Lean.Meta.mkEq source target
    let proof ← Lean.Meta.mkFreshExprMVar equality
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    scalarCongr cache 120 proof.mvarId!
    goal.assign (← Lean.Meta.mkAppM ``Eq.mp #[proof, hf])
    Lean.Elab.Tactic.replaceMainGoal []

end WeilConjectures.PurityFiniteSetting
