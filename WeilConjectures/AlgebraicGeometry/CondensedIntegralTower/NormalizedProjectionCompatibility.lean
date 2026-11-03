/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedAdjunctionCoordinates
import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedFiniteUnit

/-! # Normalization of the actual derived limit projections
(blueprint: lem-sp-normalized-projection-compatibility).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
private theorem exact_composite_factor_naturality
    {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {I J : CochainComplex C₁ ℤ} (f : I ⟶ J) :
    G.mapDerivedCategory.map (F.mapDerivedCategory.map (DerivedCategory.Q.map f)) ≫
        (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app J) ≫
          G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj J)) =
      (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app I) ≫
          G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        DerivedCategory.Q.map (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map f) := by
  have hF := F.mapDerivedCategoryFactors.hom.naturality f
  have hG := G.mapDerivedCategoryFactors.hom.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map f)
  dsimp only [Functor.comp_map] at hF hG
  rw [← Category.assoc, ← Functor.map_comp, hF, Functor.map_comp, Category.assoc, hG]
  rw [Category.assoc]
  rfl

namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

set_option maxHeartbeats 10000000 in
-- Compare the two exact localization coordinates.
private theorem factor_naturality (n : ℕ)
    {I J : CochainComplex (Towers l E T) ℤ} (f : I ⟶ J) :
    (evaluation l E T n).map (DerivedCategory.Q.map f) ≫
        (internalEvaluationFactor l E T n J).hom =
      (internalEvaluationFactor l E T n I).hom ≫ DerivedCategory.Q.map
        (((ordinaryInternalEvaluation l E T n).mapHomologicalComplex (.up ℤ)).map f) := by
  let V := SheafOfModules.systemEvaluation.{u + 1, u, u + 1} (rings l E T) n
  let e := CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj (finiteRing l E n) T)
  let := Functor.additive_of_preserves_binary_products e.inverse
  exact exact_composite_factor_naturality V e.inverse f

set_option maxHeartbeats 10000000 in
-- Comparing concrete localization coordinates requires extra definitional equality reductions.
/-- The normalized chain-map Hom correspondence identifies all actual limit projections.
Source: sk-lem-sp-tower-equivalence.proof.md, Adjunction and Counit paragraphs
(blueprint: lem-sp-normalized-projection-compatibility).
Proof: the normalized Hom correspondence fixes the derived counit. Move the limit
comparison past the scalar unit by naturality, then past the inverse level comparison.
Replace the resulting evaluated derived counit by the localized ordinary counit.
The level-counit compatibility and exact-evaluation factors leave the scalar derived
unit followed by finiteCounit, which is localization of the ordinary scalar unit.
Naturality of the exact scalar restriction cancels the remaining localization factors.
The resulting composite is exactly the definition of ordinaryLimitProjection. -/
-- Normalize the specified representative comparisons.
theorem normalized_projections_of_hom (D : Model l E T) (adj : D.red ⊣ D.rlim)
    (h : DerivedHomNormalized l E T D adj) :
    LimitProjectionsNormalized l E T D adj := by
  intro n I
  let M := (D.ordinaryLimit.mapHomologicalComplex (.up ℤ)).obj I
  let a := (upperStarFromPoint T).map (quotient l E n)
  let U : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finiteRing l E n) T) ⥤ AdicCompletion.Modules l E T :=
    Mod.comap a
  have hd := derivedCounit_of_transpose l E T D adj h I
  have hl := D.derived.levels_counit n M
  have hu := finite_unit_normalization l E T n M
  have hn := (D.levels n).inv.naturality (D.limitUnit.app I)
  dsimp only [Functor.comp_map] at hn
  have hli : (D.levels n).inv.app (DerivedCategory.Q.obj M) ≫
      (evaluation l E T n).map (D.redCounit.app M) =
        finiteCounit l E T n M ≫ (representativeLevels l E T D.ordinary n M).inv := by
    apply (cancel_mono (representativeLevels l E T D.ordinary n M).hom).mp
    rw [Category.assoc, ← hl]
    simp only [Iso.inv_hom_id_app_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hfac : (representativeLevels l E T D.ordinary n M).inv ≫
      (evaluation l E T n).map (DerivedCategory.Q.map
        ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I)) ≫
      (internalEvaluationFactor l E T n I).hom =
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (ordinaryInternalLevels l E T D.ordinary n)
        (.up ℤ)).inv.app M ≫
      ((ordinaryInternalEvaluation l E T n).mapHomologicalComplex (.up ℤ)).map
        ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I)) := by
    erw [factor_naturality l E T n
      ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I)]
    dsimp only [representativeLevels, internalEvaluationFactor, Iso.trans_inv,
      Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom]
    simp only [Category.assoc]
    erw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id_assoc, ← DerivedCategory.Q.map_comp]
    rfl
  let c := ((D.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).counit.app I)
  let κ := (NatIso.mapHomologicalComplex (ordinaryInternalLevels l E T D.ordinary n)
    (.up ℤ)).inv.app M ≫
      ((ordinaryInternalEvaluation l E T n).mapHomologicalComplex (.up ℤ)).map c
  have hn' := congrArg (fun f ↦ f ≫ (evaluation l E T n).map
    (adj.counit.app (DerivedCategory.Q.obj I)) ≫
      (internalEvaluationFactor l E T n I).hom) hn
  have hd' := congrArg (fun f ↦ (D.levels n).inv.app (DerivedCategory.Q.obj M) ≫
    (evaluation l E T n).map f ≫ (internalEvaluationFactor l E T n I).hom) hd
  have hl' := congrArg (fun f ↦ f ≫ (evaluation l E T n).map (DerivedCategory.Q.map c) ≫
    (internalEvaluationFactor l E T n I).hom) hli
  have hf' := congrArg (fun f ↦ finiteCounit l E T n M ≫ f) hfac
  simp only [Functor.map_comp, Category.assoc] at hn' hd' hl'
  have hcore : (finiteReduction l E T n).map (D.limitUnit.app I) ≫
      (D.levels n).inv.app (D.rlim.obj (DerivedCategory.Q.obj I)) ≫
      (evaluation l E T n).map (adj.counit.app (DerivedCategory.Q.obj I)) ≫
      (internalEvaluationFactor l E T n I).hom =
    finiteCounit l E T n M ≫ DerivedCategory.Q.map κ :=
      hn'.trans (hd'.trans (hl'.trans hf'))
  have hunit := (Mod.derivedExtendMapDerivedCategoryAdjunction a).unit.naturality
    (D.limitUnit.app I)
  dsimp only [Functor.id_map, Functor.comp_map] at hunit
  change D.limitUnit.app I ≫
      (Mod.derivedExtendMapDerivedCategoryAdjunction a).unit.app
        (D.rlim.obj (DerivedCategory.Q.obj I)) =
    (Mod.derivedExtendMapDerivedCategoryAdjunction a).unit.app (DerivedCategory.Q.obj M) ≫
      U.mapDerivedCategory.map ((finiteReduction l E T n).map (D.limitUnit.app I)) at hunit
  have hm := congrArg (fun f ↦ f ≫ U.mapDerivedCategory.map
      ((D.levels n).inv.app (D.rlim.obj (DerivedCategory.Q.obj I)) ≫
        (evaluation l E T n).map (adj.counit.app (DerivedCategory.Q.obj I)) ≫
          (internalEvaluationFactor l E T n I).hom) ≫
      U.mapDerivedCategoryFactors.hom.app
        (((ordinaryInternalEvaluation l E T n).mapHomologicalComplex (.up ℤ)).obj I)) hunit
  simp only [Category.assoc, ← Functor.map_comp_assoc] at hm
  rw [hcore] at hm
  dsimp only [derivedLimitProjection, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  change D.limitUnit.app I ≫
      (Mod.derivedExtendMapDerivedCategoryAdjunction a).unit.app
        (D.rlim.obj (DerivedCategory.Q.obj I)) ≫
      U.mapDerivedCategory.map ((D.levels n).inv.app (D.rlim.obj (DerivedCategory.Q.obj I))) ≫
      U.mapDerivedCategory.map ((evaluation l E T n).map
        (adj.counit.app (DerivedCategory.Q.obj I))) ≫
      U.mapDerivedCategory.map (internalEvaluationFactor l E T n I).hom ≫
      U.mapDerivedCategoryFactors.hom.app
        (((ordinaryInternalEvaluation l E T n).mapHomologicalComplex (.up ℤ)).obj I) = _
  simp only [← U.mapDerivedCategory.map_comp_assoc]
  rw [hm, U.mapDerivedCategory.map_comp, Category.assoc]
  erw [U.mapDerivedCategoryFactors_hom_naturality κ]
  erw [reassoc_of% hu, ← DerivedCategory.Q.map_comp]
  rfl

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
