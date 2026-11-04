/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalSourceTranspose
import WeilConjectures.SmoothPurity.OpenClosedIntegralSections
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

/-! # The ordinary source equation of a normalized diagonal before finite evaluation

Helper results for `exists_diagonalFiniteSource`: the supported integral unit is epic, the
scalar adjunct of a single comparison comes from an ordinary map, and the extracted ordinary map
satisfies the source equation after precomposition with the supported integral unit.
(blueprint: lem-sp-tower-class-diagonal-finite-source). -/


@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
set_option maxHeartbeats 1600000 in
-- The composite exact single comparisons need additional kernel checking time.
/-- Before finite evaluation, the extracted map already has the required ordinary
source equation after precomposition with the supported integral unit. -/
theorem diagonal_ordinarySource_precompose
    {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (hc : c.Normalized l E)
    (d : Diagonal l E b S c)
    (a : c.reduction.derived.obj
        ((DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))) ≅
      (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj
        (c.reduction.ordinary.obj
          ((constant (diagonalSurface S)).obj (diagonalIntegralSource S))))
    (ha : c.reduction.model.sourceNormalization a
      (c.reduction.model.adjunction.unit.app
        ((constant (diagonalSurface S)).obj (diagonalIntegralSource S)))) :
    let X := (constant (diagonalSurface S)).obj (diagonalIntegralSource S)
    let N := d.geometry.push.obj
      (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    let s := c.scalar.T.mapIso a.symm ≪≫ d.sourceIso ≪≫
      d.geometry.push.singleFunctorCompRightDerivedFunctorIso.app
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
    ∀ (q : c.reduction.ordinary.obj X ⟶
        (WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).obj N),
      ((c.scalar.adjunction.homEquiv _ _) s.hom ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E (diagonalSurface S))).mapDerivedCategorySingleFunctor
            0).hom.app N =
        (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Rrings l (diagonalSurface S))) 0).map q) →
    (constant (diagonalSurface S)).map (supportedIntegralUnit S) ≫
        c.reduction.model.adjunction.unit.app X ≫ c.reduction.forget.F.map q =
      integerGenerator (diagonalSurface S) (Rrings l (diagonalSurface S))
          c.reduction.forget ≫
        c.reduction.forget.F.map (scalarGenerator l E (diagonalSurface S) ≫
          (WeilConjectures.SemilinearSections.res
            (coefficientSystemMap l E (diagonalSurface S))).map
              ((d.geometry.ordinaryAdjunction.homEquiv _ _) d.coefficientPullback.iso.hom)) := by
  intro X N s q hq
  let G := c.reduction.forget.F
  let H := WeilConjectures.SemilinearSections.res
    (coefficientSystemMap l E (diagonalSurface S))
  let ad := c.reduction.model.derivedAdjunction.comp c.scalar.adjunction
  let κ := Functor.isoWhiskerRight (H.mapDerivedCategorySingleFunctor 0)
      G.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft H (G.mapDerivedCategorySingleFunctor 0)
  let t := (d.geometry.ordinaryAdjunction.homEquiv _ _) d.coefficientPullback.iso.hom
  let e := c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit
  have hfactor : c.scalar.T.map a.hom ≫ s.hom =
      d.sourceIso.hom ≫ d.geometry.push.singleFunctorCompRightDerivedFunctorIso.hom.app
        (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))) := by
    dsimp only [s]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      ← c.scalar.T.map_comp_assoc, Iso.hom_inv_id]
    erw [c.scalar.T.map_id]
    exact Category.id_comp _
  have h₁ := reduction_scalar_homEquiv_comp l E c X (c.reduction.ordinary.obj X)
    (c.reduction.model.adjunction.unit.app X) N a ha s.hom q hq
  rw [hfactor] at h₁
  have h₂ := coefficient_homEquiv_comp_eq_generators l E c hc
  have ht := diagonal_sourceIso_homEquiv l E d
  have ht' :
      (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map
          ((constant (diagonalSurface S)).map (supportedIntegralUnit S)) ≫
        (ad.homEquiv _ _) (d.sourceIso.hom ≫
          d.geometry.push.singleFunctorCompRightDerivedFunctorIso.hom.app
            (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))) =
      (ad.homEquiv _ _) (e.hom ≫
        (DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Arings l E (diagonalSurface S))) 0).map t) := by
    rw [ad.homEquiv_naturality_right, ← Category.assoc, ht,
      ← ad.homEquiv_naturality_right]
    rw [Category.assoc, unitArrow_comp_singleFunctorIso]
    rfl
  apply (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map_injective
  rw [Functor.map_comp]
  rw [← h₁]
  rw [← Category.assoc, ← Category.assoc]
  erw [ht']
  rw [ad.homEquiv_naturality_right]
  have hn := κ.hom.naturality t
  simp only [Functor.comp_map] at hn
  have hκ : (ad.homEquiv _ _) e.hom ≫ κ.hom.app
      (coefficient (diagonalSurface S) (Arings l E (diagonalSurface S))) =
    (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map
      (integerGenerator (diagonalSurface S) (Rrings l (diagonalSurface S))
        c.reduction.forget ≫ G.map (scalarGenerator l E (diagonalSurface S))) := h₂
  simp only [Category.assoc]
  change (ad.homEquiv _ _) e.hom ≫ G.mapDerivedCategory.map
      (H.mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (Systems (diagonalSurface S)
          (Arings l E (diagonalSurface S))) 0).map t)) ≫ κ.hom.app N = _
  erw [hn]
  rw [← Category.assoc, hκ]
  simp only [Functor.map_comp, Category.assoc]
  rfl


end AlgebraicGeometry.ProEtale.SpTowerClasses
