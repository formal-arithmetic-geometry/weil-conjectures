/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryForgetComparison
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAuxDerived

/-! # Ordinary source equation before finite evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Two normalized adjunction transposes give the composite ordinary source map. -/
private theorem reduction_scalar_transpose
    {T : Scheme.{u}} (c : Chern l E T) (X : Ab T)
    (M : Systems T (Rrings l T)) (q₀ : X ⟶ c.reduction.forget.F.obj M)
    (N : Systems T (Arings l E T))
    (a : c.reduction.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        M)
    (ha : c.reduction.model.sourceNormalization a q₀)
    (s : c.scalar.T.obj
        ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
          M) ⟶
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj N)
    (q : M ⟶
      (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N)
    (hs : (c.scalar.adjunction.homEquiv _ _) s ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map q) :
    ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _)
        (c.scalar.T.map a.hom ≫ s) ≫
      c.reduction.forget.F.mapDerivedCategory.map
        (((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
        ((WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N) =
    (DerivedCategory.singleFunctor (Ab T) 0).map
      (q₀ ≫ c.reduction.forget.F.map q) := by
  rw [Adjunction.comp_homEquiv]
  change (c.reduction.model.derivedAdjunction.homEquiv _ _)
      ((c.scalar.adjunction.homEquiv _ _) (c.scalar.T.map a.hom ≫ s)) ≫ _ = _
  erw [c.scalar.adjunction.homEquiv_naturality_left,
    c.reduction.model.derivedAdjunction.homEquiv_naturality_right]
  simp only [Category.assoc, ← c.reduction.forget.F.mapDerivedCategory.map_comp_assoc]
  rw [hs]
  erw [(c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.naturality q]
  rw [← Category.assoc, ha]
  simp only [Functor.comp_map, Functor.map_comp]

/-- The composite coefficient unit has the prescribed ordinary integer generator. -/
private theorem coefficient_source_transpose
    {T : Scheme.{u}} (c : Chern l E T) (hc : c.Normalized l E) :
    let e := c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit
    ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _)
        e.hom ≫
      c.reduction.forget.F.mapDerivedCategory.map
        (((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app
            (coefficient T (Arings l E T))) ≫
      (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
        ((WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj
          (coefficient T (Arings l E T))) =
    (DerivedCategory.singleFunctor (Ab T) 0).map
      (integerGenerator T (Rrings l T) c.reduction.forget ≫
        c.reduction.forget.F.map (scalarGenerator l E T)) := by
  exact reduction_scalar_transpose l E c (integers T) (coefficient T (Rrings l T))
    (integerGenerator T (Rrings l T) c.reduction.forget) (coefficient T (Arings l E T))
    c.unitIso hc.1 c.scalarUnit.hom (scalarGenerator l E T) hc.2.2

/-- The supplied geometric source equation remains exact after both adjunctions. -/
private theorem diagonal_source_transpose
    {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (d : Diagonal l E b S c) :
    let k := (DerivedCategory.singleFunctor (Ab (diagonalSurface S)) 0).map
      ((constant (diagonalSurface S)).map (supportedIntegralUnit S))
    let ad := c.reduction.model.derivedAdjunction.comp c.scalar.adjunction
    let e := c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit
    k ≫ (ad.homEquiv _ _) d.sourceIso.hom =
      (ad.homEquiv _ _) (e.hom ≫ unitArrow l E d.coefficientPullback) := by
  dsimp only
  rw [← Adjunction.homEquiv_naturality_left]
  apply congrArg ((c.reduction.model.derivedAdjunction.comp
    c.scalar.adjunction).homEquiv _ _)
  rw [← d.source_normalization]
  unfold diagonalExtendedUnit
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, ← c.scalar.T.map_comp_assoc,
    ]

end AlgebraicGeometry.ProEtale.SpTowerClasses
