/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalNatTrans
import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidalUnit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-! # The tensor-unit equation for the pro-étale compactification projection -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open DerivedCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.OrderedProjectionUnit

variable (B : Type v) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]

private def nativeUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar B f).leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  letI := (upperStar B f).leftDerivedFunctorMonoidal
  (Functor.Monoidal.εIso (upperStar B f).leftDerivedFunctor).symm

private theorem tensor_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B)) :
    letI := (upperStar B f).leftDerivedFunctorMonoidal
    Functor.OplaxMonoidal.δ (upperStar B f).leftDerivedFunctor K L =
      ((leftDerivedUpperStarTensorComparison B f).app K).app L := by
  rw [leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison]
  exact (upperStar B f).leftDerivedFunctorMonoidal_δ K L

private theorem native_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B)) :
    ((leftDerivedUpperStarTensorComparison B f).app K).app (𝟙_ _) ≫
      (upperStar B f).leftDerivedFunctor.obj K ◁ (nativeUnit B f).hom ≫
      (ρ_ _).hom = (upperStar B f).leftDerivedFunctor.map (ρ_ K).hom := by
  let := (upperStar B f).leftDerivedFunctorMonoidal
  rw [← tensor_comparison]
  exact Functor.OplaxMonoidal.right_unitality_hom _ K

private theorem proper_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    ((rightDerivedLowerStarProjectionMap B f).app M).app (𝟙_ _) ≫
      (lowerStar B f).rightDerivedFunctor.map
        (M ◁ (nativeUnit B f).hom ≫ (ρ_ M).hom) = (ρ_ _).hom := by
  rw [Functor.map_comp]
  exact (derivedUpperStarLowerStarAdjunction B f).rightAdjointProjectionMap_rightUnitality
    _ _ (native_right_unit B f) M

private theorem native_eta_eq {W V : Scheme.{u}} (h : W ⟶ V) :
    have := DerivedCategory.isIso_ε_Qh (Sheaf (Scheme.ProEt.topology W) B)
    (nativeUnit B h).hom =
      (upperStar B h).leftDerivedFunctor.map
          (Functor.LaxMonoidal.ε (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology V) B))) ≫
        (upperStar B h).leftDerivedFunctorCounit.app (𝟙_ _) ≫
        DerivedCategory.Qh.map
          (Functor.OplaxMonoidal.η ((upperStar B h).mapHomotopyCategory (.up ℤ))) ≫
        inv (Functor.LaxMonoidal.ε
          (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology W) B))) := by
  rfl

set_option maxHeartbeats 800000 in
-- Compare the units through the three derived counits.
private theorem native_comp_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [NatTrans.IsMonoidal (upperStarComp B f g).hom] :
    (leftDerivedUpperStarComp B f g).hom.app (𝟙_ _) ≫
        (upperStar B f).leftDerivedFunctor.map (nativeUnit B g).hom ≫
        (nativeUnit B f).hom = (nativeUnit B (f ≫ g)).hom := by
  rw [native_eta_eq, native_eta_eq, native_eta_eq]
  have := DerivedCategory.isIso_ε_Qh (Sheaf (Scheme.ProEt.topology Y) B)
  have e₁ : (L((f)^*[B])).map ((L((g)^*[B])).map (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫
        (g)^*[B].leftDerivedFunctorCounit.app (𝟙_ _) ≫
          DerivedCategory.Qh.map
            (Functor.OplaxMonoidal.η ((g)^*[B].mapHomotopyCategory (.up ℤ))) ≫
            inv (Functor.LaxMonoidal.ε DerivedCategory.Qh)) ≫
        (L((f)^*[B])).map (Functor.LaxMonoidal.ε DerivedCategory.Qh) =
      (L((f)^*[B])).map ((L((g)^*[B])).map (Functor.LaxMonoidal.ε DerivedCategory.Qh)) ≫
        (L((f)^*[B])).map ((g)^*[B].leftDerivedFunctorCounit.app (𝟙_ _)) ≫
          (L((f)^*[B])).map (DerivedCategory.Qh.map
            (Functor.OplaxMonoidal.η ((g)^*[B].mapHomotopyCategory (.up ℤ)))) := by
    simp only [← Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hn : (L((f)^*[B])).map (DerivedCategory.Qh.map
        (Functor.OplaxMonoidal.η ((g)^*[B].mapHomotopyCategory (.up ℤ)))) ≫
        (f)^*[B].leftDerivedFunctorCounit.app (𝟙_ _) =
      (f)^*[B].leftDerivedFunctorCounit.app (((g)^*[B].mapHomotopyCategory (.up ℤ)).obj (𝟙_ _)) ≫
        DerivedCategory.Qh.map (((f)^*[B].mapHomotopyCategory (.up ℤ)).map
          (Functor.OplaxMonoidal.η ((g)^*[B].mapHomotopyCategory (.up ℤ)))) :=
    (f)^*[B].leftDerivedFunctorCounit.naturality _
  have hc : (leftDerivedUpperStarComp B f g).hom.app (𝟙_ _) ≫
        (L((f)^*[B])).map ((L((g)^*[B])).map (Functor.LaxMonoidal.ε DerivedCategory.Qh)) =
      (L((f ≫ g)^*[B])).map (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫
        (leftDerivedUpperStarComp B f g).hom.app (DerivedCategory.Qh.obj (𝟙_ _)) :=
    ((leftDerivedUpperStarComp B f g).hom.naturality _).symm
  have hX := (leftDerivedUpperStarComp_hom_app_Qh_obj_comp_counit B f g (𝟙_ _)).symm
  have hu := Functor.mapHomotopyCategoryCompNatTrans_η (g)^*[B] (f)^*[B] (f ≫ g)^*[B]
    (upperStarComp B f g).hom
  have e₂ := congrArg DerivedCategory.Qh.map hu
  simp only [Functor.map_comp] at e₂
  rw [reassoc_of% e₁, reassoc_of% hn, reassoc_of% hc, ← reassoc_of% hX]
  rw [← e₂]
  simp only [Category.assoc]
  rfl

private theorem inv_native_right_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) B)) :
    (upperStar B f).leftDerivedFunctor.obj K ◁ (nativeUnit B f).inv ≫
      inv (((leftDerivedUpperStarTensorComparison B f).app K).app (𝟙_ _)) ≫
      (upperStar B f).leftDerivedFunctor.map (ρ_ K).hom = (ρ_ _).hom := by
  rw [← native_right_unit, IsIso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

private theorem open_tensor_right_unit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    (upperStar B j).mapDerivedCategory.obj M ◁ (nativeUnit B j).inv ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso B j).hom.app M).app (𝟙_ _) ≫
        (upperStar B j).mapDerivedCategory.map (ρ_ M).hom = (ρ_ _).hom := by
  have hh : ((mapDerivedCategoryUpperStarDerivedTensorIso B j).hom.app M).app (𝟙_ _) =
      (leftDerivedUpperStarIsoMapDerivedCategory B j).inv.app M ▷
          (upperStar B j).leftDerivedFunctor.obj (𝟙_ _) ≫
        inv (((leftDerivedUpperStarTensorComparison B j).app M).app (𝟙_ _)) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory B j).hom.app (M ⊗ 𝟙_ _) := by
    have hi : ((leftDerivedUpperStarTensorNatIso B j).inv.app M).app (𝟙_ _) =
        inv (((leftDerivedUpperStarTensorComparison B j).app M).app (𝟙_ _)) :=
      IsIso.eq_inv_of_hom_inv_id
        (f := ((leftDerivedUpperStarTensorComparison B j).app M).app (𝟙_ _))
        (((leftDerivedUpperStarTensorNatIso B j).app M).app (𝟙_ _)).hom_inv_id
    rw [← hi]
    rfl
  rw [hh, Category.assoc, Category.assoc,
    ← (leftDerivedUpperStarIsoMapDerivedCategory B j).hom.naturality,
    whisker_exchange_assoc]
  erw [reassoc_of% inv_native_right_unit B j M]
  rw [rightUnitor_naturality_assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem open_right_unit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : DerivedCategory (Sheaf (Scheme.ProEt.topology U) B)) :
    ((derivedOpenImmersionLowerShriekProjectionIso B j).inv.app K).app (𝟙_ _) ≫
      (openImmersionLowerShriek B j).mapDerivedCategory.map
        (K ◁ (nativeUnit B j).hom ≫ (ρ_ K).hom) = (ρ_ _).hom := by
  have h := (derivedOpenImmersionLowerShriekUpperStarAdjunction B j).projectionMap_rightUnitality
    _ _ (nativeUnit B j).inv (open_tensor_right_unit B j) K
  change (openImmersionLowerShriek B j).mapDerivedCategory.map
      ((ρ_ K).inv ≫ K ◁ (nativeUnit B j).inv) ≫
    ((derivedOpenImmersionLowerShriekProjectionIso B j).hom.app K).app (𝟙_ _) = _ at h
  rw [← cancel_epi (ρ_ ((openImmersionLowerShriek B j).mapDerivedCategory.obj K)).inv,
    Iso.inv_hom_id, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_app_app_assoc, ← Functor.map_comp,
    ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp,
    Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id]

omit [UpperStarPreservesFlat B] in
private theorem unit_hom_comp_ε {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (leftDerivedUpperStarUnitIso B g).hom ≫
        Functor.LaxMonoidal.ε (Qh (C := Sheaf (Scheme.ProEt.topology Z) B)) =
    L((g)^*[B]).map (Functor.LaxMonoidal.ε (Qh (C := Sheaf (Scheme.ProEt.topology Y) B))) ≫
      (g)^*[B].leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (Functor.OplaxMonoidal.mapHomotopyCategoryη (.up ℤ) (g)^*[B]) := by
  have h₁ : Functor.LaxMonoidal.ε (Qh (C := Sheaf (Scheme.ProEt.topology Z) B)) = 𝟙 _ := rfl
  have h₂ : Functor.LaxMonoidal.ε (Qh (C := Sheaf (Scheme.ProEt.topology Y) B)) = 𝟙 _ := rfl
  rw [← (g)^*[B].leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  dsimp [leftDerivedUpperStarUnitIso]
  simp only [h₁, h₂, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc]
  change _ ≫ _ = (g)^*[B].leftDerivedFunctorIsoMapDerivedCategory.hom.app _ ≫ _
  congr 1
  erw [(g)^*[B].mapDerivedCategoryFactorsh_hom_app (𝟙_ _)]
  simp only [Functor.OplaxMonoidal.mapHomotopyCategoryη,
    Functor.OplaxMonoidal.mapHomologicalComplexη, Functor.Monoidal.εIso_inv, Functor.map_comp,
    Q_obj_single_obj, Functor.comp_obj, Category.assoc]
  have h₃ : ∀ K, (quotientCompQhIso (Sheaf (Scheme.ProEt.topology Y) B)).hom.app K = 𝟙 _ :=
    fun _ ↦ rfl
  have h₄ : ∀ K, (quotientCompQhIso (Sheaf (Scheme.ProEt.topology Z) B)).inv.app K = 𝟙 _ :=
    fun _ ↦ rfl
  have h₅ : ∀ K, ((g)^*[B].mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K = 𝟙 _ :=
    fun _ ↦ rfl
  erw [h₃, h₄, h₅, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp]
  have h₆ : ∀ {K L : CochainComplex (Sheaf (Scheme.ProEt.topology Z) B) ℤ} (f : K ⟶ L),
      Qh.map ((HomotopyCategory.quotient _ _).map f) = Q.map f := fun f ↦ by
    have h := quotientCompQhIso_hom_naturality f
    have h₃' : ∀ K, (quotientCompQhIso (Sheaf (Scheme.ProEt.topology Z) B)).hom.app K = 𝟙 _ :=
      fun _ ↦ rfl
    rw [h₃', h₃'] at h
    exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  erw [Category.id_comp, h₆, h₆]
  rw [h₆]
  rfl

private theorem native_unit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (nativeUnit B f).hom = (leftDerivedUpperStarUnitIso B f).hom := by
  have := DerivedCategory.isIso_ε_Qh (Sheaf (Scheme.ProEt.topology X) B)
  apply (cancel_mono (Functor.LaxMonoidal.ε
    (Qh (C := Sheaf (Scheme.ProEt.topology X) B)))).1
  rw [native_eta_eq, Category.assoc, Category.assoc, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id, unit_hom_comp_ε]
  rfl

namespace UnitCongruence
open Lean Elab Tactic Meta

private meta def projectionHead (e : Expr) : MetaM Expr := do
  let .proj structName idx value := e.getAppFn | return e
  let valueType ← withTransparency .default (whnf (← inferType value))
  let .const actualName _ := valueType.getAppFn |
    throwError "unexpected projection structure type {valueType}"
  unless actualName == structName do
    throwError "projection type did not reduce to {structName}: {valueType}"
  let fields := getStructureFields (← getEnv) structName
  let some fieldName := fields[idx]? | throwError "missing structure projection"
  let fn ← mkAppOptM (structName ++ fieldName)
    ((valueType.getAppArgs.push value).map some)
  instantiateMVars (mkAppN fn e.getAppArgs)

private meta def projectionNormalize (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  if let .letE _ _ value body _ := e then return body.instantiate1 value
  if e.getAppFn.isConstOf ``Functor.comp then
    let args := e.getAppArgs
    let f := args[6]!
    if f.getAppFn.isConstOf ``Functor.comp then
      let inner := f.getAppArgs
      let tail ← mkAppM ``Functor.comp #[inner[7]!, args[7]!]
      return ← mkAppM ``Functor.comp #[inner[6]!, tail]
  if let some n := e.getAppFn.constName? then
    let aliases := ["canonicalTensorSymmetry", "curriedBraidingNatIso", "compProjectionMap",
      "rightDerivedLowerStarProjectionMap", "rightDerivedLowerShriekOfCompactification",
      "derivedTensor", "curriedTensor_obj_map"]
    if aliases.contains n.getString! then
      if let some e' ← withTransparency .default (unfoldDefinition? e) then
        return ← instantiateMVars e'
  if e.getAppFn.isConstOf ``Functor.obj || e.getAppFn.isConstOf ``Functor.map then
    return ← withTransparency .default (whnf e)
  projectionHead e

private meta def baseScheme? (e : Expr) : Option Expr := do
  guard (e.getAppFn.isConstOf ``DerivedCategory)
  let sh ← e.getAppArgs[0]?
  guard (sh.getAppFn.isConstOf ``Sheaf)
  let site ← sh.getAppArgs[0]?
  guard (site.getAppFn.isConstOf ``Scheme.ProEt)
  site.getAppArgs[0]?

private meta partial def projectionCached (a b : Expr) :
    StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
  let key := (a.consumeMData, b.consumeMData)
  if let some pf := (← get).get? key then return pf
  let compute (_ : Unit) : StateRefT (Std.HashMap (Expr × Expr) Expr) MetaM Expr := do
    if a.consumeMData == b.consumeMData then return ← mkHEqRefl a
    if a.getAppFn != b.getAppFn then
      let an ← projectionNormalize a
      if an != a then
        let haType ← mkAppM ``HEq #[a, an]
        let ha ← mkAuxTheorem haType (← mkHEqRefl a)
          (zetaDelta := true) (kind? := `_unitReduction)
        let hn ← projectionCached an b
        let pf ← mkAppM ``HEq.trans #[ha, hn]
        return ← mkAuxTheorem (← inferType pf) pf
          (zetaDelta := true) (kind? := `_projection)
      let bn ← projectionNormalize b
      if bn != b then
        let hbType ← mkAppM ``HEq #[b, bn]
        let hb ← mkAuxTheorem hbType (← mkHEqRefl b)
          (zetaDelta := true) (kind? := `_unitReduction)
        let hn ← projectionCached a bn
        let pf ← mkAppM ``HEq.trans #[hn, ← mkAppM ``HEq.symm #[hb]]
        return ← mkAuxTheorem (← inferType pf) pf
          (zetaDelta := true) (kind? := `_projection)
    if a.getAppFn.isConstOf ``Functor.comp || b.getAppFn.isConstOf ``Functor.comp then
      let an ← projectionNormalize a
      if an != a then
        let haType ← mkAppM ``HEq #[a, an]
        let ha ← mkAuxTheorem haType (← mkHEqRefl a)
          (zetaDelta := true) (kind? := `_unitReduction)
        let hn ← projectionCached an b
        let pf ← mkAppM ``HEq.trans #[ha, hn]
        return ← mkAuxTheorem (← inferType pf) pf
          (zetaDelta := true) (kind? := `_projection)
      let bn ← projectionNormalize b
      if bn != b then
        let hbType ← mkAppM ``HEq #[b, bn]
        let hb ← mkAuxTheorem hbType (← mkHEqRefl b)
          (zetaDelta := true) (kind? := `_unitReduction)
        let hn ← projectionCached a bn
        let pf ← mkAppM ``HEq.trans #[hn, ← mkAppM ``HEq.symm #[hb]]
        return ← mkAuxTheorem (← inferType pf) pf
          (zetaDelta := true) (kind? := `_projection)
    let mut normalize := false
    if a.getAppFn == b.getAppFn &&
        (a.getAppFn.isConstOf ``Functor.obj || a.getAppFn.isConstOf ``Functor.map) then
      match baseScheme? a.getAppArgs[0]!, baseScheme? b.getAppArgs[0]! with
      | some sa, some sb => normalize := sa.consumeMData != sb.consumeMData
      | _, _ => pure ()
    if normalize then
      let an ← projectionNormalize a
      if an != a then
        let haType ← mkAppM ``HEq #[a, an]
        let ha ← mkAuxTheorem haType (← mkHEqRefl a)
          (zetaDelta := true) (kind? := `_unitReduction)
        let hn ← projectionCached an b
        let pf ← mkAppM ``HEq.trans #[ha, hn]
        return ← mkAuxTheorem (← inferType pf) pf
          (zetaDelta := true) (kind? := `_projection)
      let bn ← projectionNormalize b
      if bn != b then
        let hbType ← mkAppM ``HEq #[b, bn]
        let hb ← mkAuxTheorem hbType (← mkHEqRefl b)
          (zetaDelta := true) (kind? := `_unitReduction)
        let hb ← mkAppM ``HEq.symm #[hb]
        let hn ← projectionCached a bn
        let pf ← mkAppM ``HEq.trans #[hn, hb]
        return ← mkAuxTheorem (← inferType pf) pf
          (zetaDelta := true) (kind? := `_projection)
    if ← isProp (← inferType a) then
      return ← mkAppM ``proof_irrel_heq #[a, b]
    if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
      let argsA := a.getAppArgs
      let argsB := b.getAppArgs
      let ct ← mkHCongrWithArity a.getAppFn argsA.size
      let mut ps := #[]
      for i in [:argsA.size] do
        let mut h ← projectionCached argsA[i]! argsB[i]!
        if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
        ps := ps ++ #[argsA[i]!, argsB[i]!, h]
      let pf := mkAppN ct.proof ps
      let pf ← if (← inferType pf).isHEq then pure pf else mkAppM ``heq_of_eq #[pf]
      return ← mkAuxTheorem (← inferType pf) pf
        (zetaDelta := true) (kind? := `_projection)
    unless ← withTransparency .default (isDefEq a b) do
      throwError m!"Different projection expressions: {a} versus {b}; \
        heads {a.getAppFn} versus {b.getAppFn}; \
        right arguments {(b.getAppArgs.map fun x ↦ x.getAppFn)}"
    return ← mkHEqRefl a
  let pf ← compute ()
  modify (·.insert key pf)
  return pf

private meta def projectionCongrHEq (a b : Expr) : MetaM Expr :=
  (projectionCached a b).run' {}


private meta partial def foldedHEq (a b : Expr) : MetaM Expr := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then return ← mkHEqRefl a
  if ← isProp (← inferType a) then
    return ← mkAppM ``proof_irrel_heq #[a, b]
  if a.getAppFn == b.getAppFn && a.getAppArgs.size == b.getAppArgs.size then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    let ct ← mkHCongrWithArity a.getAppFn argsA.size
    let mut ps := #[]
    for i in [:argsA.size] do
      let mut h ← try foldedHEq argsA[i]! argsB[i]! catch ex =>
        throwError m!"Argument {i} of {a.getAppFn}: {ex.toMessageData}"
      if ct.argKinds[i]! == .eq then h ← mkAppM ``eq_of_heq #[h]
      ps := ps ++ #[argsA[i]!, argsB[i]!, h]
    let pf := mkAppN ct.proof ps
    if (← inferType pf).isHEq then return pf
    else return ← mkAppM ``heq_of_eq #[pf]
  unless ← withTransparency .default (isDefEq a b) do
    throwError m!"Different folded unit expressions: {a} versus {b}"
  return ← mkHEqRefl a

private meta def close (name : Name) (folded : Bool := false) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let decls := (← getLCtx).decls.toList.filterMap id
  let some d := decls.find? (fun d ↦ d.userName.eraseMacroScopes == name) |
    throwError "missing unit comparison {name}"
  let source ← instantiateMVars d.type
    let h ← if folded then foldedHEq target source else projectionCongrHEq target source
  let e ← mkAppM ``eq_of_heq #[h]
  let pf ← mkAppM ``Eq.mpr #[e, d.toExpr]
  (← getMainGoal).assign pf

end UnitCongruence

set_option allowUnsafeReducibility true in
attribute [local irreducible] _root_.DerivedCategory instCategoryDerivedCategory

attribute [local irreducible] projectionMapOfCompactification rightDerivedLowerStarProjectionMap
  leftDerivedUpperStarTensorComparison DerivedCategory.braidedCategory'
attribute [local irreducible] nativeUnit Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Functor.rightDerivedFunctor HasDerivedCategory.ofIsGrothendieckAbelian
  leftDerivedUpperStarComp leftDerivedUpperStarCompactificationIso
  derivedUpperStarLowerStarAdjunction derivedOpenImmersionLowerShriekProjectionIso
  Adjunction.rightAdjointProjectionMap
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private theorem inv_native_comp_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [NatTrans.IsMonoidal (upperStarComp B f g).hom] :
    (leftDerivedUpperStarComp B f g).inv.app (𝟙_ _) ≫
      (nativeUnit B (f ≫ g)).hom =
      (upperStar B f).leftDerivedFunctor.map (nativeUnit B g).hom ≫
        (nativeUnit B f).hom := by
  rw [← native_comp_unit B f g, Iso.inv_hom_id_app_assoc]

private theorem transported_comp_unit {X Z Y : Scheme.{u}}
    (i : X ⟶ Z) (g : Z ⟶ Y) {f : X ⟶ Y} (w : i ≫ g = f)
    [NatTrans.IsMonoidal (upperStarComp B i g).hom] :
    ((leftDerivedUpperStarComp B i g).symm ≪≫
      eqToIso (congrArg (fun k ↦ (upperStar B k).leftDerivedFunctor) w)).hom.app (𝟙_ _) ≫
        (nativeUnit B f).hom =
      (upperStar B i).leftDerivedFunctor.map (nativeUnit B g).hom ≫
        (nativeUnit B i).hom := by
  subst f
  simp only [eqToIso_refl, Iso.trans_refl, Iso.symm_hom]
  exact inv_native_comp_unit B i g

private theorem compactification_unit {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [NatTrans.IsMonoidal (upperStarComp B c.i c.g).hom] :
    (leftDerivedUpperStarCompactificationIso B c).hom.app (𝟙_ _) ≫
      (nativeUnit B f).hom =
      (upperStar B c.i).leftDerivedFunctor.map (nativeUnit B c.g).hom ≫
        (nativeUnit B c.i).hom := by
  have ht := transported_comp_unit B c.i c.g c.comm.symm
  unfold leftDerivedUpperStarCompactificationIso
  run_tac UnitCongruence.close `ht true

private theorem comp_eq_transfer
    {C : Type*} [Category C] {X Y Z : C} {p q : X ⟶ Y}
    {a : Y ⟶ Z} {b : X ⟶ Z} (he : p = q) (hq : q ≫ a = b) : p ≫ a = b := by
  rw [he]
  exact hq

private theorem open_naturality {X Z : Scheme.{u}} (i : X ⟶ Z) [IsOpenImmersion i]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B))
    {N N' : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) B)} (y : N ⟶ N') :
    (openImmersionLowerShriek B i).mapDerivedCategory.obj K ◁ y ≫
      ((derivedOpenImmersionLowerShriekProjectionIso B i).inv.app K).app N' =
      ((derivedOpenImmersionLowerShriekProjectionIso B i).inv.app K).app N ≫
        (openImmersionLowerShriek B i).mapDerivedCategory.map
          (K ◁ (upperStar B i).leftDerivedFunctor.map y) := by
  have hn := ((derivedOpenImmersionLowerShriekProjectionIso B i).inv.app K).naturality y
  simpa only [derivedTensorWhiskeringLeftOpenImmersionLowerShriek,
    derivedTensorWhiskeringRightLeftDerivedUpperStar, derivedTensor,
    Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringRight,
    Functor.whiskeringLeft, Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    curriedTensor_obj_obj, curriedTensor_obj_map] using hn

private theorem paste_right_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) (G : E ⥤ D) (F' : E ⥤ C) (J : C ⥤ E) (F'' : D ⥤ C)
    (p : ∀ (M : E) (N : D), G.obj M ⊗ N ⟶ G.obj (M ⊗ F.obj N))
    (ψ : ∀ (K : C) (N : E), J.obj K ⊗ N ⟶ J.obj (K ⊗ F'.obj N))
    (e : ∀ N : D, F'.obj (F.obj N) ⟶ F''.obj N)
    (η : F.obj (𝟙_ D) ⟶ 𝟙_ E) (η' : F'.obj (𝟙_ E) ⟶ 𝟙_ C)
    (η'' : F''.obj (𝟙_ D) ⟶ 𝟙_ C)
    (hp : ∀ M : E, p M (𝟙_ D) ≫ G.map (M ◁ η ≫ (ρ_ M).hom) = (ρ_ _).hom)
    (hψr : ∀ (K : C) {N N' : E} (y : N ⟶ N'),
      J.obj K ◁ y ≫ ψ K N' = ψ K N ≫ J.map (K ◁ F'.map y))
    (hψ : ∀ K : C, ψ K (𝟙_ E) ≫ J.map (K ◁ η' ≫ (ρ_ K).hom) = (ρ_ _).hom)
    (he : e (𝟙_ D) ≫ η'' = F'.map η ≫ η') (K : C) :
    (p (J.obj K) (𝟙_ D) ≫ G.map (ψ K (F.obj (𝟙_ D))) ≫
      G.map (J.map (K ◁ e (𝟙_ D)))) ≫ (J ⋙ G).map (K ◁ η'' ≫ (ρ_ K).hom) =
      (ρ_ _).hom := by
  simp only [Category.assoc, Functor.comp_map, ← G.map_comp, ← J.map_comp,
    ← MonoidalCategory.whiskerLeft_comp_assoc, he]
  rw [MonoidalCategory.whiskerLeft_comp_assoc, J.map_comp, ← reassoc_of% (hψr K η),
    G.map_comp, ← G.map_comp, hψ]
  exact hp (J.obj K)

set_option maxHeartbeats 400000 in
-- Paste the component equations without unfolding the derived constructions.
private theorem native_compact_right_unit {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [NatTrans.IsMonoidal (upperStarComp B c.i c.g).hom]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    ((projectionMapOfCompactification B c).app K).app (𝟙_ _) ≫
      (rightDerivedLowerShriekOfCompactification B c).map
        (K ◁ (nativeUnit B f).hom ≫ (ρ_ K).hom) = (ρ_ _).hom := by
  refine comp_eq_transfer (projectionMapOfCompactification_app_app B c K (𝟙_ _)) ?_
  have h := paste_right_unit (upperStar B c.g).leftDerivedFunctor
    (lowerStar B c.g).rightDerivedFunctor (upperStar B c.i).leftDerivedFunctor
    (openImmersionLowerShriek B c.i).mapDerivedCategory (upperStar B f).leftDerivedFunctor
    (fun M N ↦ ((rightDerivedLowerStarProjectionMap B c.g).app M).app N)
    (fun M N ↦ ((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app M).app N)
    (fun N ↦ (leftDerivedUpperStarCompactificationIso B c).hom.app N)
    (nativeUnit B c.g).hom (nativeUnit B c.i).hom (nativeUnit B f).hom
    (proper_right_unit B c.g)
    (open_naturality B c.i)
    (open_right_unit B c.i) (compactification_unit B c) K
  dsimp only [rightDerivedLowerShriekOfCompactification,
    derivedTensorRightDerivedLowerShriek, rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar,
    derivedTensor, Functor.postcompose₂, Functor.whiskeringLeft₂, Functor.whiskeringRight,
    Functor.whiskeringLeft, Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    curriedTensor_obj_obj, curriedTensor_obj_map] at h ⊢
  run_tac UnitCongruence.close `h false


private theorem projection_unit_congr
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (Q : C ⥤ D) (K I : C) (p : Q.obj K ⊗ 𝟙_ D ⟶ Q.obj (K ⊗ I))
    (η η' : I ⟶ 𝟙_ C) (he : η = η')
    (hp : p ≫ Q.map (K ◁ η ≫ (ρ_ K).hom) = (ρ_ (Q.obj K)).hom) :
    p ≫ Q.map (K ◁ η' ≫ (ρ_ K).hom) = (ρ_ (Q.obj K)).hom := by
  cases he
  exact hp

/-- The native compactification projection respects the right tensor unit.
Source: blueprint def-exchange-projection, projection transformation, and monoidal
unit coherence of inverse image (blueprint: lem-pur-native-projection-unit).
Proof: derive the inverse-image monoidal unit law. Apply the adjunction triangle
through rightAdjointProjectionMap_rightUnitality to obtain the proper equation.
Apply the dual adjunction equation to extension by zero and invert its projection
isomorphism. The inverse-image compositor preserves the unit by its homotopy
category counit factorization and the unit law of the underived compositor.
Paste the two projection equations using naturality of the open projection. -/
theorem compactification_right_unit {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [NatTrans.IsMonoidal (upperStarComp B c.i c.g).hom]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) B)) :
    ((projectionMapOfCompactification B c).app K).app (𝟙_ _) ≫
      (rightDerivedLowerShriekOfCompactification B c).map
        (K ◁ (leftDerivedUpperStarUnitIso B f).hom ≫ (ρ_ K).hom) = (ρ_ _).hom := by
  exact projection_unit_congr (rightDerivedLowerShriekOfCompactification B c) K _
    (((projectionMapOfCompactification B c).app K).app (𝟙_ _))
    (nativeUnit B f).hom (leftDerivedUpperStarUnitIso B f).hom (native_unit_eq B f)
    (native_compact_right_unit B c K)

end AlgebraicGeometry.ProEtale.OrderedProjectionUnit
