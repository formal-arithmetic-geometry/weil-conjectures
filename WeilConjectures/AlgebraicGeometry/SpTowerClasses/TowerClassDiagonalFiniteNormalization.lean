/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassDiagonalFiniteSource
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerClassSupportedReductionComparison
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralChernNormalization
import WeilConjectures.AlgebraicGeometry.ScalarData.ScalarModelUnit
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Normalized.NormalizedScalarArrow
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.ScalarRootTranspose
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryEndpointMaps

/-! # Finite normalization of the supported positive diagonal -/

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

private theorem supported_finite_square
    {T : Scheme.{u}} (c : Chern l E T) (hc : c.Normalized l E)
    (X : Ab T)
    (a : c.reduction.derived.obj ((DerivedCategory.singleFunctor (Ab T) 0).obj X) ≅
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        (c.reduction.ordinary.obj X))
    (ha : c.reduction.model.sourceNormalization a (c.reduction.model.adjunction.unit.app X))
    (N : Systems T (Arings l E T))
    (s : c.scalar.T.obj
        ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
          (c.reduction.ordinary.obj X)) ≅
      (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).obj N)
    (q : c.reduction.ordinary.obj X ⟶
      (WeilConjectures.SemilinearSections.res (coefficientSystemMap l E T)).obj N)
    (hs : (c.scalar.adjunction.homEquiv _ _) s.hom ≫
        ((WeilConjectures.SemilinearSections.res
          (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app N =
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map q)
    (beta : (DerivedCategory.singleFunctor (Ab T) 0).obj X ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T))⟦(1 : ℤ)⟧) (n : ℕ) :
    let f := a.inv ≫ c.reduction.derived.map beta ≫ c.rootIso.hom
    let b := s.inv ≫ c.scalar.T.map f ≫
      (c.scalar.T.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj c.rootModule) ≫
      (lineComparison l E c)⟦(2 : ℤ)⟧'
    let source := (abEvaluation T n).map (c.reduction.model.adjunction.unit.app X) ≫
      (c.reduction.forget.F ⋙ abEvaluation T n).map q ≫
      (finiteScalarForgetIso l E c n).hom.app N
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).map source ≫
        (mapSingleArrow (SpTowerShriek.ev l E T n ⋙ finiteForget l E T n) (2 : ℤ) b ≫
          ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
            ((finiteForget l E T n).map (lineEvaluation l E c n).hom))⟦(2 : ℤ)⟧') =
      mapSingleArrow (abEvaluation T n) (2 : ℤ)
          (kummerComposite (towerKummerComplex l c.kummer)
            (towerKummerShortExact l c.kummer) beta) ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (finiteRootMap l E T n))⟦(2 : ℤ)⟧' := by
  intro f b source
  let F := c.reduction.forget.F
  let V := abEvaluation T n
  let G := WeilConjectures.SemilinearSections.res.{u + 1, u, u + 1}
    (coefficientSystemMap l E T)
  let H := SpTowerShriek.ev l E T n ⋙ finiteForget l E T n
  let e := finiteScalarForgetIso l E c n
  have had : c.scalar.adjunction.CommShift ℤ := by
    rw [c.scalar.adjunction_eq]
    exact (SheafOfModules.sheafScalarDerivedAdjunction
      (coefficientSystemMap l E T) c.scalar.model).commShift_of_rightAdjoint ℤ
  let : c.scalar.adjunction.CommShift ℤ := had
  have hy := scalarRootTranspose l E c
  simp only [Adjunction.homEquiv_unit, Category.assoc] at hs hy
  have hscalar := normalizedScalarArrow_transpose c.scalar.T G.mapDerivedCategory
    c.scalar.adjunction s (lineComparison l E c)
    ((G.mapDerivedCategorySingleFunctor 0).app N)
    ((G.mapDerivedCategorySingleFunctor 0).app (lineModule l E c))
    _ _ hs hy (2 : ℤ) f
  have hscalar' :
      (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map q ≫
        mapSingleArrow G (2 : ℤ) b = f ≫
          ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map
            (c.scalar.ordinaryAdjunction.unit.app c.rootModule))⟦(2 : ℤ)⟧' := by
    exact hscalar
  have hintegral := normalizedDerivedExtension_arrow c.reduction.model
    (towerKummerComplex l c.kummer) (towerKummerShortExact l c.kummer)
    a c.rootIso c.rootForget (c.reduction.model.adjunction.unit.app X) ha hc.2.1 beta
  have hev := congrArg (fun z ↦ mapSingleArrow V (2 : ℤ) z) hintegral
  rw [map_underlyingSingleArrow] at hev
  have h := finiteBoundary_exact_glue F V G H e
    (V.map (c.reduction.model.adjunction.unit.app X)) q
    (c.scalar.ordinaryAdjunction.unit.app c.rootModule) (V.mapIso c.rootForget)
    ((finiteForget l E T n).map (lineEvaluation l E c n).hom) b f hscalar'
  have hi :
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (V.map (c.reduction.model.adjunction.unit.app X)) ≫
        mapSingleArrow (F ⋙ V) (2 : ℤ) f ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (V.map c.rootForget.hom))⟦(2 : ℤ)⟧') =
      mapSingleArrow V (2 : ℤ)
        (kummerComposite (towerKummerComplex l c.kummer)
          (towerKummerShortExact l c.kummer) beta) := by
    exact hev
  simp only [Functor.mapIso_hom, Functor.mapIso_inv] at h
  rw [hi] at h
  dsimp only [V, F, e] at h
  erw [finiteBoundary_rootMap l E c n] at h
  exact h

/-- The supported class made from normalized Chern data has the actual finite
positive Kummer boundary at every level.

Source: latest blueprint classes proof (3), step 13 of
`lem-sp-prescribed-projective-class-package`.
(blueprint: lem-sp-tower-class-diagonal-finite-normalization).

Proof: use the reduction adjunction unit on the constant supported integer
source, followed by the scalar adjunction unit. Exact forgetting and evaluation
identify their composite with the canonical supported finite quotient: after
ordinaryPushEvaluation it sends every local integer k to k times one. The
source normalization fixes this identification for the supplied geometric
adjunction. To check it, precompose with the supported integral unit, use the
source and scalar unit normalizations, and apply faithfulness of the degree-zero
single functor; the integral restriction is epic for a closed immersion.
The target normalization is the positive Kummer boundary on the whole unit
tower. The transpose formula for the universal scalar counit on the root
module inserts one tensor the root, and lineEvaluation identifies it with the
prescribed finite root map. Naturality moves the supported Cartier boundary
through the two adjunctions, giving quotient followed by evaluatedDiagonal
equals the evaluated positive Kummer composite followed by finiteRootMap.
Transport the endpoints with the exact single and shift comparisons. These
are the witnesses in singleBoundaryEquality. This calculation is performed at
each level and never infers equality of derived maps from their evaluations. -/
theorem diagonal_finite_normalization {b : SpTowerShriek.Base l E}
    {S : Scheme.{u}} [IsNoetherian S]
    {c : Chern l E (diagonalSurface S)} (hc : c.Normalized l E)
    (d : Diagonal l E b S c) : FiniteDiagonalNormalization l E d := by
  obtain ⟨a, ha⟩ := supportedReduction_comparison l S c.reduction
  let X := (constant (diagonalSurface S)).obj (diagonalIntegralSource S)
  let N := d.geometry.push.obj
    (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
  let s := c.scalar.T.mapIso a.symm ≪≫ d.sourceIso ≪≫
    (d.geometry.push.singleFunctorCompRightDerivedFunctorIso).app
      (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))
  obtain ⟨q, hq, hsource⟩ := exists_diagonalFiniteSource l E hc d a ha
  let f := a.inv ≫ c.reduction.derived.map (diagonalBoundary S) ≫ c.rootIso.hom
  let gamma := s.inv ≫ c.scalar.T.map f ≫
    (c.scalar.T.commShiftIso (2 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor (Systems (diagonalSurface S)
        (Rrings l (diagonalSurface S))) 0).obj c.rootModule) ≫
    (lineComparison l E c)⟦(2 : ℤ)⟧'
  have hdiag : gamma =
      (d.geometry.push.singleFunctorCompRightDerivedFunctorIso).inv.app
          (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))) ≫
        diagonalArrow l E c d.sourceIso := by
    dsimp only [gamma, s, f]
    unfold diagonalArrow
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc,
      ← c.scalar.T.map_comp_assoc, Iso.hom_inv_id_assoc]
    rfl
  intro n
  have heval : mapSingleArrow (finiteForget l E (diagonalSurface S) n) (2 : ℤ)
      (evaluatedDiagonal l E d n) =
    mapSingleArrow
        (SpTowerShriek.ev l E (diagonalSurface S) n ⋙
          finiteForget l E (diagonalSurface S) n) (2 : ℤ) gamma ≫
      ((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface S)) 0).map
        ((finiteForget l E (diagonalSurface S) n).map
          (lineEvaluation l E c n).hom))⟦(2 : ℤ)⟧' := by
    rw [hdiag]
    unfold evaluatedDiagonal
    rw [mapSingleArrow_postcompose, mapSingleArrow_composite]
  have h := supported_finite_square l E c hc X a ha N s q hq (diagonalBoundary S) n
  dsimp only at h
  rw [hsource n] at h
  refine ⟨_, _, HEq.rfl, HEq.rfl, ?_⟩
  rw [heval]
  exact h

end AlgebraicGeometry.ProEtale.SpTowerClasses
