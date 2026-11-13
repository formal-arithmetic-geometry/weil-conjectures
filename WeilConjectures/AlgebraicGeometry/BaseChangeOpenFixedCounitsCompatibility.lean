/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeSquare
import WeilConjectures.AlgebraicGeometry.ModulePullbackComparisonDegreeAutomorphism
/-! General open restriction compatibility used by fixed counits. -/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
private theorem pinned_comparison_isComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (k : X ⟶ Y) [(Scheme.Modules.tensorPullback k).Additive]
    (M : Y.Modules) (n : ℤ) :
    IsModulePullbackComparisonInDegree k M n (pinnedSingleDegreeTensorComparison k M n) := by
  classical
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k
  refine ⟨ε, ?_, rfl⟩
  exact Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) k

set_option linter.unusedVariables false in
-- Keep the original comparison-proof binder hc0; it is introduced again after the lets.
set_option maxHeartbeats 1000000 in
-- Elaborating the explicit comparison witnesses needs a larger heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Open restriction compatibility for single modules in every integer degree.
Source: Stacks Project, Tags 08FE and 08HY.
Generalizes the degree-zero compatibility statement of
CanonicalModuleBaseChangeOpenComparisonCompat, whose proof imports the fixed-counit
item and therefore cannot be imported here without a cycle. -/
theorem restricted_base_change_compatibility_single_degree
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules) (n : ℤ)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : (∃ ε : DerivedCategory.Qh.{w} ⋙ derivedPullback g' ⟶
          (Scheme.Modules.tensorPullback g').mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh.{w} (C := SheafOfModules.{u}
              (moduleRings X'.toRingedSpace)),
        (derivedPullback g').IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ∧
          c = cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor _ n).obj G) ≫
            DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex
                (Scheme.Modules.tensorPullback g') (ComplexShape.up ℤ) n).hom.app G)))))
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    let U := f ⁻¹ᵁ V
    let fA := f ∣_ V
    let gA := g.resLE V W hWV
    let H := (schemeOpenRestriction X U).obj G
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G
    let E0 := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj H
    let R := (schemeOpenRestriction S' W).mapDerivedCategory
    ∀ (c0 : (derivedPullback (pullback.fst fA gA)).obj E0 ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) n).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj H))
    (hc0 : (∃ ε : DerivedCategory.Qh.{w} ⋙ derivedPullback (pullback.fst fA gA) ⟶
          (Scheme.Modules.tensorPullback (pullback.fst fA gA)).mapHomotopyCategory
              (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh.{w} (C := SheafOfModules.{u}
              (moduleRings (pullback fA gA).toRingedSpace)),
        (derivedPullback (pullback.fst fA gA)).IsLeftDerivedFunctor ε
            (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ∧
          c0 = cast (by rfl) (ε.app ((HomotopyCategory.singleFunctor _ n).obj H) ≫
            DerivedCategory.Qh.{w}.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex
                (Scheme.Modules.tensorPullback (pullback.fst fA gA))
                  (ComplexShape.up ℤ) n).hom.app H))))),
      ∃ a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)) ≅
          (derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E0),
      ∃ b : R.obj ((schemeDerivedDirectImage f').obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n).obj
                ((Scheme.Modules.tensorPullback g').obj G))) ≅
          (schemeDerivedDirectImage (pullback.snd fA gA)).obj
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) n).obj
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
  let H : U.toScheme.Modules := (schemeOpenRestriction X U).obj G
  let p := pullback.fst fA gA
  let q := pullback.snd fA gA
  let c₁ := pinnedSingleDegreeTensorComparison.{u, w} g' G n
  let c₂ := pinnedSingleDegreeTensorComparison.{u, w} p H n
  have hc₁ : IsModulePullbackComparisonInDegree g' G n c₁ :=
    pinned_comparison_isComparison g' G n
  have hc₂ : IsModulePullbackComparisonInDegree p H n c₂ :=
    pinned_comparison_isComparison p H n
  obtain ⟨α, hα⟩ :=
    modulePullbackComparison_degree_target_automorphism.{u, w} g' G n c₁ c hc₁ hc
  obtain ⟨γ, hγ⟩ :=
    modulePullbackComparison_degree_target_automorphism.{u, w} p H n c₂ c0 hc₂ hc0
  obtain ⟨a, b, hb⟩ := open_pinned_single_degree_square.{u, w} f g g' f' sq n V W hWV
  let R := (schemeOpenRestriction S' W).mapDerivedCategory
  let T := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n
  let T0 := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) n
  let A := R.mapIso ((schemeDerivedDirectImage f').mapIso (T.mapIso α))
  let B := (schemeDerivedDirectImage q).mapIso (T0.mapIso γ)
  refine ⟨a.app G, A.symm ≪≫ b.app G ≪≫ B, ?_⟩
  have h :
      (R.map (schemeDerivedBaseChangeMap f f' g g' sq.w _ ≫
        (schemeDerivedDirectImage f').map c₁) ≫ A.hom) ≫
          (A.symm ≪≫ b.app G ≪≫ B).hom =
        (a.app G).hom ≫
          ((schemeDerivedBaseChangeMap fA q gA p pullback.condition _ ≫
            (schemeDerivedDirectImage q).map c₂) ≫ B.hom) := by
    simpa only [R, U, fA, gA, H, p, q, c₁, c₂, Functor.comp_obj, Iso.app_hom,
      Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using
      congrArg (fun k => k ≫ B.hom) (hb G)
  simpa only [A, B, R, T, T0, U, fA, gA, H, p, q, Functor.comp_obj, c₁, c₂, hα, hγ,
    Functor.map_comp, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc] using h

end AlgebraicGeometry
