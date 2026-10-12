/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Sheaf.AlgebraicGeometry.BaseChangeOpenFixedCounits
import Sheaf.AlgebraicGeometry.ModulePullbackComparisonTargetAutomorphism
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
private theorem conjugateSquare {C : Type*} [Category* C]
    {L L0 N N0 : C} (m : L ⟶ N) (n : L0 ⟶ N0)
    (a : L ≅ L0) (b : N ≅ N0) (A : N ≅ N) (B : N0 ≅ N0)
    (h : m ≫ b.hom = a.hom ≫ n) :
    (m ≫ A.hom) ≫ (A.symm ≪≫ b ≪≫ B).hom = a.hom ≫ (n ≫ B.hom) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem canonicalTensorComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (k : X ⟶ Y) [(Scheme.Modules.tensorPullback k).Additive]
    (M : Y.Modules) :
    let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k))
      |>.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction k)
    IsDerivedModulePullbackComparison k M
      (Scheme.Modules.canonicalSinglePullbackMap k M ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (t.inv.app M)) := by
  classical
  intro t
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  refine ⟨ε, ?_, ?_⟩
  · exact Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  · have ht := t.hom_inv_id_app M
    dsimp only [Scheme.Modules.canonicalSinglePullbackMap]
    erw [Category.assoc, Category.assoc, ← Functor.map_comp, ht]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

set_option linter.unusedVariables false in
-- Keep the original universally quantified comparison-proof binder hc0 unchanged.
set_option maxHeartbeats 1000000 in
-- Comparing the restricted derived-category witnesses needs extra elaboration heartbeats.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compatibility of restriction isomorphisms with the canonical base-change map.
Source: Stacks Project, Tags 08FE, 08HY, 08IB.
(blueprint: lem-pc-canonical-module-base-change-open-comparison-compat) -/
theorem restricted_base_change_compatibility
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    let U := f ⁻¹ᵁ V
    let fA := f ∣_ V
    let gA := g.resLE V W hWV
    let H := (schemeOpenRestriction X U).obj G
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let E0 := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj H
    let R := (schemeOpenRestriction S' W).mapDerivedCategory
    ∀ (c0 : (derivedPullback (pullback.fst fA gA)).obj E0 ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H))
    (hc0 : IsDerivedModulePullbackComparison (pullback.fst fA gA) H c0),
      ∃ a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≅
          (derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E0),
      ∃ b : R.obj ((schemeDerivedDirectImage f').obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback g').obj G))) ≅
          (schemeDerivedDirectImage (pullback.snd fA gA)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H)),
        R.map (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
            (schemeDerivedDirectImage f').map c) ≫ b.hom =
          a.hom ≫
            (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
              pullback.condition E0 ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
       := by
  classical
  dsimp only
  intro c0 hc0
  let U := f ⁻¹ᵁ V
  let fA := f ∣_ V
  let gA := g.resLE V W hWV
  let H : (f ⁻¹ᵁ V).toScheme.Modules := (schemeOpenRestriction X U).obj G
  let p := pullback.fst fA gA
  let q := pullback.snd fA gA
  let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g'))
    |>.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g')
  let t0 := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p))
    |>.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction p)
  let c₁ := Scheme.Modules.canonicalSinglePullbackMap.{u, w} g' G ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map (t.inv.app G)
  let c₂ := Scheme.Modules.canonicalSinglePullbackMap.{u, w} p H ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).map (t0.inv.app H)
  have hc₁ : IsDerivedModulePullbackComparison g' G c₁ := canonicalTensorComparison g' G
  have hc₂ : IsDerivedModulePullbackComparison p H c₂ := canonicalTensorComparison p H
  obtain ⟨α, hα⟩ := modulePullbackComparison_target_automorphism.{u, w} g' G c₁ c hc₁ hc
  obtain ⟨γ, hγ⟩ := modulePullbackComparison_target_automorphism.{u, w} p H c₂ c0 hc₂ hc0
  obtain ⟨a, b, hb⟩ := restricted_base_change_fixed_counits.{u, w} f g g' f' sq G V W hWV
  let R := (schemeOpenRestriction S' W).mapDerivedCategory
  let T := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0
  let T0 := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0
  let A := R.mapIso ((schemeDerivedDirectImage f').mapIso (T.mapIso α))
  let B := (schemeDerivedDirectImage q).mapIso (T0.mapIso γ)
  refine ⟨a, A.symm ≪≫ b ≪≫ B, ?_⟩
  have h := conjugateSquare _ _ a b A B hb
  simpa only [A, B, R, T, T0, c₁, c₂, hα, hγ, Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.trans_hom, Iso.symm_hom, Category.assoc] using h
end AlgebraicGeometry
