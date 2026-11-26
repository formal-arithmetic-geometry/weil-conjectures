/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses

/-!
# Compact-support reduction tower datum

The datum `CompactSupportReductionTowerConstruction` of a coherent compact-support tower,
its level evaluations, and the right-derived inverse limit used to define integral
compact-support pushforward.

## Implementation details

The tower, its evaluations, and the derived inverse-limit functor are fields of one datum,
so downstream definitions do not choose them independently from an existence proposition.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures

/-- The coherent tower and normalized derived limit used for compact support: a linear
triangulated tower functor whose evaluations are the restricted compact-support levels,
compatibly with transitions at every pair of levels, together with a right-derived inverse
limit and its normalized projections. -/
structure CompactSupportReductionTowerConstruction
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E Y))] where
  tower : DerivedCategory (scalarReductionSource l E X) ⥤
    DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y))
  evaluations : ∀ m : ℕ,
    tower ⋙ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) m ≅
      compactSupportRestrictedLevel l E c m
  /-- The evaluation isomorphisms carry every tower transition to the
  prescribed quotient and compact-support transition. -/
  transition_compatibility :
    ∀ (m n : ℕ) (h : n ≤ m) (K : DerivedCategory (scalarReductionSource l E X)),
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y)
          m n h).app (tower.obj K) ≫ (evaluations n).hom.app K =
        (evaluations m).hom.app K ≫ compactSupportRestrictedTransition l E c m n h K
  /-- The source and target coefficient categories carry the normalized scalar
  actions used in the reduction construction. -/
  sourceLinear : Linear (Padic.coefficientExtensionIntegers l E)
    (scalarReductionSource l E X)
  targetLinear : Linear (Padic.coefficientExtensionIntegers l E)
    (scalarReductionSource l E Y)
  sourceScalarAction : @IsCompactSupportScalarAction l _ E _ _ _ X sourceLinear
  targetScalarAction : @IsCompactSupportScalarAction l _ E _ _ _ Y targetLinear
  /-- The coherent tower functor is linear and triangulated. -/
  towerLinear : tower.Linear (Padic.coefficientExtensionIntegers l E)
  towerShift : ∃ (_shift : tower.CommShift ℤ), tower.IsTriangulated
  limit : DerivedCategory (pbcTowers Y
      (completedIntegralCommRingSheafUnrestricted l E Y)) ⥤
    DerivedCategory (scalarReductionSource l E Y)
  limitUnit :
    (lim : pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y) ⥤
      scalarReductionSource l E Y).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ limit
  limit_isRightDerived :
    limit.IsRightDerivedFunctor limitUnit
      (HomologicalComplex.quasiIso
        (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y))
        (ComplexShape.up ℤ))
  limit_isIso_on_KInjective :
    ∀ I : CochainComplex
      (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) ℤ,
      CochainComplex.IsKInjective I → IsIso (limitUnit.app I)
  projections : ∀ m : ℕ,
    limit ⟶ pbcTowerEvaluation Y
      (completedIntegralCommRingSheafUnrestricted l E Y) m
  projection_normalization :
    ∀ (m : ℕ)
      (I : CochainComplex
        (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) ℤ),
      limitUnit.app I ≫ (projections m).app (DerivedCategory.Q.obj I) ≫
        (Functor.mapDerivedCategoryFactors
          ((evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op m))).hom.app I =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op m)) (ComplexShape.up ℤ)).app I)

end WeilConjectures
