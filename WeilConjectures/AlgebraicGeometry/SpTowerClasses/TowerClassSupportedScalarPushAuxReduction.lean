/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassSupportedScalarPushAux
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAuxDerived
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSourceAuxPrecompose

/-! # Reduction of the supported scalar push comparison to ordinary systems -/

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

/-- The ordinary source map after the supported unit, read through the composite
reduction/scalar transpose and the exact single comparisons. -/
private theorem scalar_reduction_source_left {T : Scheme.{u}} (c : Chern l E T)
    (X : Ab T) (N : Systems T (Arings l E T))
    (a : c.reduction.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj (c.reduction.ordinary.obj X))
    (ha : c.reduction.model.sourceNormalization a (c.reduction.model.adjunction.unit.app X))
    (s : c.scalar.T.obj ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        (c.reduction.ordinary.obj X)) ⟶
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj N)
    (q : c.reduction.ordinary.obj X ⟶
      (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N)
    (hs : (c.scalar.adjunction.homEquiv _ _) s ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map q)
    (k : integers T ⟶ X) :
    ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _)
        (c.scalar.T.map (c.reduction.derived.map
          ((DerivedCategory.singleFunctor (Ab T) 0).map k)) ≫ c.scalar.T.map a.hom ≫ s) ≫
      c.reduction.forget.F.mapDerivedCategory.map
        (((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
        ((WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N) =
    (DerivedCategory.singleFunctor (Ab T) 0).map
      (k ≫ c.reduction.model.adjunction.unit.app X ≫ c.reduction.forget.F.map q) := by
  have h₁ := reduction_scalar_transpose l E c X (c.reduction.ordinary.obj X)
    (c.reduction.model.adjunction.unit.app X)
    N a ha s q hs
  erw [Adjunction.homEquiv_naturality_left]
  rw [Category.assoc]
  erw [h₁]
  simp only [Functor.map_comp]

/-- The coefficient side: the scalar-extended unit followed by an ordinary coefficient
map, read through the same transpose and comparisons. -/
private theorem scalar_reduction_source_right {T : Scheme.{u}} (c : Chern l E T)
    (hc : c.Normalized l E) (N : Systems T (Arings l E T))
    (t : coefficient T (Arings l E T) ⟶ N) :
    ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _)
        ((c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit).hom ≫
          (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).map t) ≫
      c.reduction.forget.F.mapDerivedCategory.map
        (((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
        ((WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N) =
    (DerivedCategory.singleFunctor (Ab T) 0).map
      (integerGenerator T (Rrings l T) c.reduction.forget ≫
        c.reduction.forget.F.map (scalarGenerator l E T ≫
          (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).map t)) := by
  let H := WeilConjectures.SemilinearSections.res.{u + 1, u, u + 1}
    (coefficientSystemMap l E T)
  let G := c.reduction.forget.F
  let κ := Functor.isoWhiskerRight (H.mapDerivedCategorySingleFunctor 0)
      G.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft H (G.mapDerivedCategorySingleFunctor 0)
  have h₂ := coefficient_source_transpose l E c hc
  have hn := κ.hom.naturality t
  simp only [Functor.comp_map] at hn
  have hκ : ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _)
      (c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit).hom ≫
        κ.hom.app (coefficient T (Arings l E T)) =
      (DerivedCategory.singleFunctor (Ab T) 0).map
        (integerGenerator T (Rrings l T) c.reduction.forget ≫
          G.map (scalarGenerator l E T)) := h₂
  rw [Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]
  change _ ≫ G.mapDerivedCategory.map
      (H.mapDerivedCategory.map
        ((DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).map t)) ≫
      κ.hom.app N = _
  erw [hn]
  rw [← Category.assoc, hκ]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- An ordinary source equation after a map from the integers gives the derived
scalar-extended source equation.

Proof: compare both sides after the composite reduction/scalar transpose and the
invertible exact single comparisons. -/
theorem scalar_reduction_source_eq {T : Scheme.{u}} (c : Chern l E T)
    (hc : c.Normalized l E)
    (X : Ab T) (N : Systems T (Arings l E T))
    (a : c.reduction.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj (c.reduction.ordinary.obj X))
    (ha : c.reduction.model.sourceNormalization a (c.reduction.model.adjunction.unit.app X))
    (s : c.scalar.T.obj ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        (c.reduction.ordinary.obj X)) ⟶
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj N)
    (q : c.reduction.ordinary.obj X ⟶
      (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N)
    (hs : (c.scalar.adjunction.homEquiv _ _) s ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map q)
    (k : integers T ⟶ X) (t : coefficient T (Arings l E T) ⟶ N)
    (h : k ≫ c.reduction.model.adjunction.unit.app X ≫ c.reduction.forget.F.map q =
      integerGenerator T (Rrings l T) c.reduction.forget ≫
        c.reduction.forget.F.map (scalarGenerator l E T ≫
          (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).map t)) :
    c.scalar.T.map (c.reduction.derived.map
        ((DerivedCategory.singleFunctor (Ab T) 0).map k)) ≫ c.scalar.T.map a.hom ≫ s =
      (c.scalar.T.mapIso c.unitIso ≪≫ c.scalarUnit).hom ≫
        (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).map t := by
  apply ((c.reduction.model.derivedAdjunction.comp c.scalar.adjunction).homEquiv _ _).injective
  rw [← cancel_mono (c.reduction.forget.F.mapDerivedCategory.map
      (((WeilConjectures.SemilinearSections.res
        (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N) ≫
    (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
      ((WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N)),
    scalar_reduction_source_left l E c X N a ha s q hs k,
    scalar_reduction_source_right l E c hc N t, h]

end AlgebraicGeometry.ProEtale.SpTowerClasses
