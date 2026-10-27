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

/-- Invertibility and commutativity on strict coefficient-system complexes.
Source: Stacks 0959, 03QP; the finite-stalk permutation sentence of
blueprint sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-zl-finite-pushforward.proof.md,
and steps 2--4 of lem-zl-finite-restriction-diagram-naturality
(blueprint: lem-zl-finite-restriction-strict-transport).

Proof: inverse image along u, w, c and the fibre isomorphism is an equivalence
of coefficient-system categories. Its coefficient identifications fix every constant
section and quotient projection. The direct-image mates in source and middle
are therefore invertible. For sum, pullback along c preserves products; reindex
by the equivalence points and use stalk on each projection. Reverse reindexing
and the inverse stalk maps give its inverse, including the empty product.
Transpose both composites of the exchange square under the h-adjunction.
The mate formula writes each transpose as the pullback of the f-counit.
The equations of geometry identify the paths, and naturality of the counit
identifies the transposes. Injectivity of the adjunction bijection proves the square.
For restriction, compose with every point-product projection. Its component is
the pullback of the h-counit. The equation point_paths identifies the two sections
of the fibre product, so counit naturality gives the component square. The defining
projection equation of sum and product extensionality give the restriction square.
These are equations of whole system morphisms, hence also of their termwise
complex maps; no finiteness, reducedness or nonempty-fibre assumption is used. -/
theorem finiteRestrictionStrictTransport
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {k : Type u} [Field k] (G : Diagram k) :
    IsIso (source l E G) ∧ IsIso (middle l E G) ∧ IsIso (sum l E G) ∧
    ∀ T : CochainComplex (coefficientSequenceModules l E G.X') ℤ,
      (exchangeSquare l E G T).Commutes ∧ (restrictionSquare l E G T).Commutes := by
  sorry

end WeilConjectures.FiniteRestrictionNaturality
