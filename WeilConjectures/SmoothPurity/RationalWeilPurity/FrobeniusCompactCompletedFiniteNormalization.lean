/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import WeilConjectures.SmoothPurity.RationalWeilPurity.RationalWeilPurityNaturalityMate
public import WeilConjectures.SmoothPurity.FrobeniusExchange.FrobeniusCompactFiniteCoordinates

/-! # Finite normalization of the completed-coefficient compact Frobenius mate

Source: blueprint, compact-support transport in the counit square, and its
coefficient-reduction compatibility in Steps 2 and 5 of
`thm-pur-weil-equivariance-of-purity-and-trace.proof.md`.
(blueprint: lem-pur-frobenius-compact-completed-finite-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalWeilPurity

attribute [local irreducible] HasDerivedCategory.standard scalarReductionDerivedExistence
  completedIntegralCoefficientSheafUnrestricted FrobeniusExchange.models integralExchange
attribute [local implicit_reducible] constructibleIntegralPullback

/-- Reducing the completed-coefficient mate gives the actual finite proper/open mate.

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
`thm-pur-weil-equivariance-of-purity-and-trace.proof.md`, Step 2, and the
coefficient-normalized compact transport of def-zl-frobenius-compact-support-comparison.

Proof: compute on one flat-term K-flat input resolution and simultaneous K-injective
proper-image resolutions, at the fixed positive quotient exponent n+1. The unit
normalization of completedToOrdinary identifies its reduction with the pullback
reduction counit, evaluated and changed to tensor-pullback coordinates; this is
finitePullCoordinates. The projection equations of sfQcqsCompactSupportRealization
identify the two support realizations with the recorded finite support coordinates.
Transpose the coefficient-reduction square through the proper adjunction: the
reduced unit, square and counit are the finite proper mate. For the open factor,
transpose through the exact open adjunction; its unit is the identity on the open
and both extensions vanish outside it, so the reduced inverse open mate is the
finite open exchange. Paste the two factor equations. The adjacent realization
and pullback coordinate comparisons cancel, leaving compactFiniteCoordinates.
All comparisons come from the same quotient system and commute with its transitions;
no equality is inferred from faithfulness of evaluation. The formula also holds at
n=0 (exponent one), on the zero object, and for empty or identity factors.
(blueprint: lem-pur-frobenius-compact-completed-finite-normalization). -/
theorem integralExchange_finiteCoordinates
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c₀ : Compactification f₀.left)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) (n : ℕ) :
    letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
      (FrobeniusExchange.fiber_finiteType D X₀).1
    letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
      (FrobeniusExchange.fiber_finiteType D X₀).2
    letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
      (FrobeniusExchange.fiber_finiteType D Y₀).1
    letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
      (FrobeniusExchange.fiber_finiteType D Y₀).2
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
    letI := (FrobeniusExchange.fiberMap_properties D f₀).1
    letI := (FrobeniusExchange.fiberMap_properties D f₀).2.1
    letI := (FrobeniusExchange.fiberMap_properties D f₀).2.2
    let c : Compactification (X := (D.geometricFiber X₀).left)
        (Y := (D.geometricFiber Y₀).left) (FrobeniusExchange.fiberMap D f₀) :=
      FrobeniusExchange.geometricCompactification D f₀ c₀
    let Q := (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom).obj M
    (scalarReductionDerivedExtension l E (D.geometricFiber Y₀).left n).map
        (integralExchange D l hl f₀ E c₀ M).hom.hom ≫
      (sfCompactSupportFiniteReductionIso l D.k (zlClosurePrimeUnit D l hl) c E Q n).hom =
    FrobeniusExchange.compactFiniteCoordinates
      (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
      l E D.k (zlClosurePrimeUnit D l hl)
      (FrobeniusExchange.fiberMap D f₀) c (D.geometricFrobenius X₀).hom
      (D.geometricFrobenius (zlCompactificationMiddle D f₀ c₀)).hom
      (D.geometricFrobenius Y₀).hom
      (D.frobenius_square_cartesian _ _ (zlCompactificationProper D f₀ c₀)).2.2.2.2.1
      (D.frobenius_square_cartesian _ _ (zlCompactificationOpen D f₀ c₀)).2.2.2.2.2.1
      M n := by sorry

end WeilConjectures.RationalWeilPurity
