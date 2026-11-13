/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
import WeilConjectures.AlgebraicGeometry.BaseChangeOpenFixedCounitsCompatibility
/-! # Open restriction for the fixed derived pullback counits
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
-/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical comparison is obtained by the chosen derived counit.
Source: Stacks Project, Tag 08HY. -/
private theorem canonical_single_pullback_comparison_fixed
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X Y : Scheme.{u}} (g' : X ⟶ Y) (G : Y.Modules) :
    let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g')).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction g')
    IsDerivedModulePullbackComparison g' G
      (Scheme.Modules.canonicalSinglePullbackMap g' G ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map (t.inv.app G))  := by
  classical
  intro t
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) g'
  refine ⟨ε, ?_, ?_⟩
  · exact Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) g'
  · have ht := t.hom_inv_id_app G
    dsimp only [Scheme.Modules.canonicalSinglePullbackMap]
    erw [Category.assoc, ← Functor.map_comp, ht]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The explicit fixed-counit restriction statement. -/
def fixedCounitRestrictionStatement
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules) (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) : Prop :=
  let U := f ⁻¹ᵁ V
  let fA := f ∣_ V
  let gA := g.resLE V W hWV
  let H := (schemeOpenRestriction X U).obj G
  let E := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
  let E0 := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj H
  let R := (schemeOpenRestriction S' W).mapDerivedCategory
  let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g'))
    |>.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g')
  let t0 := (Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.fst fA gA)))
      |>.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction (pullback.fst fA gA))
  let c := Scheme.Modules.canonicalSinglePullbackMap g' G ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map (t.inv.app G)
  let c0 := Scheme.Modules.canonicalSinglePullbackMap (pullback.fst fA gA) H ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).map
        (t0.inv.app H)
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
/-- Open restriction for the fixed counits used to define the derived base-change map
(Stacks, Tags 08FE, 08HY, 08IB, 0D5U). -/
theorem restricted_base_change_fixed_counits
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules) (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    fixedCounitRestrictionStatement f g g' f' sq G V W hWV := by
  classical
  dsimp [fixedCounitRestrictionStatement]
  let t := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g')).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction g')
  let c := Scheme.Modules.canonicalSinglePullbackMap g' G ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map (t.inv.app G)
  have hc : IsDerivedModulePullbackComparison g' G c := by
    exact canonical_single_pullback_comparison_fixed g' G
  let U := f ⁻¹ᵁ V
  let fA := f ∣_ V
  let gA := g.resLE V W hWV
  let H := (schemeOpenRestriction X U).obj G
  let p := pullback.fst fA gA
  let t0 := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction p)
  let c0 := Scheme.Modules.canonicalSinglePullbackMap p H ≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).map (t0.inv.app H)
  have hc0 : IsDerivedModulePullbackComparison p H c0 := by
    exact canonical_single_pullback_comparison_fixed p H
  simpa [c, t, c0, t0, U, fA, gA, H, p] using
    (restricted_base_change_compatibility_single_degree f g g' f' sq G 0 c hc V W hWV c0 hc0)
end AlgebraicGeometry
