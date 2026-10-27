/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.FiniteRestrictionDiagramModels

/-! # Finite-fibre transport: a step of semilinear diagram naturality -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence SheafOfModules.monoidalCategory

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.FiniteRestrictionNaturality
open FiniteCounitTowers

/-- Constructibility of the vertices of the two completed strict squares.
Source: Bhatt--Scholze, Sections 6.5 and 6.7; Stacks 0941;
steps 2 and 6 of lem-zl-finite-restriction-diagram-naturality
(blueprint: lem-zl-finite-restriction-constructible-vertices).

Proof: the presentation identifies the localized strict system T with the derived
reduction of K. Reindexing along u transports its flat-term K-flat representative
and every quotient map. The finite integral fibre reconstruction theorem identifies
the completed B and C vertices with point pullback of finite direct image and
finite direct image of fibre pullback, respectively. Both are constructible by
finite direct-image preservation and integral constructible pullback preservation.
The completed D vertex is the finite biproduct of completed point pullbacks;
finite biproducts preserve constructibility. The reindexing completion comparison
identifies the primed vertices after c-pullback with the same constructions on
the transported input. Isomorphism invariance transfers constructibility through
the specified comparisons. All statements concern objects only: commutativity of
exchange and restriction is a separate step. Empty fibres give zero biproducts,
which are constructible; the argument does not replace a nonreduced fibre by its
reduction. -/
theorem finiteRestrictionConstructibleVertices
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (G : Diagram F.k)
    [IsSeparated G.aX] [LocallyOfFiniteType G.aX] [QuasiCompact G.aX]
    [IsSeparated G.aY] [LocallyOfFiniteType G.aY] [QuasiCompact G.aY]
    [IsSeparated G.aX'] [LocallyOfFiniteType G.aX'] [QuasiCompact G.aX']
    [IsSeparated G.aY'] [LocallyOfFiniteType G.aY'] [QuasiCompact G.aY']
    [IsFinite G.f] [IsFinite G.f']
    (K : sfIntegralConstructibleCategory l E G.X')
      (Q : CochainComplex (scalarReductionSource.{u, u} l E G.X') ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := Scheme.ProEt.topology G.X')
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E G.X') Q)
      (hflat : ∀ j : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := Scheme.ProEt.topology G.X')
        (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E G.X') (Q.X j))
      (eQ : DerivedCategory.Q.obj Q ≅ K.obj)
      (T : CochainComplex (coefficientSequenceModules l E G.X') ℤ)
      (κ : ∀ n : ℕ, (level l E G.X' n).obj T ≅
        ((scalarReductionExtension.{u, u} l E G.X' n).mapHomologicalComplex (.up ℤ)).obj Q)
      (eT : (coefficientDerivedSystemEvaluationCalculus.{u, u} l E G.X').choose.reduction.obj
        (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj T)
      (hT : CoefficientReductionPresentation.{u, u} l E G.X'
        (CoefficientDerivedSystemFibers.toCoefficientDerivedSystemReduction.{u, u}
          (CoefficientDerivedSystemCalculus.toCoefficientDerivedSystemFibers.{u, u}
            (coefficientDerivedSystemEvaluationCalculus.{u, u} l E G.X').choose)) Q hQ T eT κ) :
    (completed l E (exchangeSquare l E G T)).Vertices
      (sfIntegralConstructible l E (Spec (.of F.k))) ∧
    (completed l E (restrictionSquare l E G T)).Vertices
      (sfIntegralConstructible l E (Spec (.of F.k))) := by
  sorry

end WeilConjectures.FiniteRestrictionNaturality
