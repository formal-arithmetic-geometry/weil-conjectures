/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module

public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.SystemOperationExchangeRealization

/-! # Projection-normalized transpose before the final reduction isomorphism

Source: lem-fix-operation-reduction, compact-support and final paragraphs.
(blueprint: lem-sf-compact-support-realized-scalar-transpose-projection)

This is the transpose equation with the target reduction isomorphism removed from
both sides.  The original statement follows by composing with that isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The realized scalar transpose, before postcomposition with the chosen target
reduction projection.  This is the projection-normalized geometric mate equation;
composing with the target projection recovers the finite-stage equation.  Its proof
expands the proper/open system mate, uses the scalar evaluation square and the
naturality of the completed mixed unit, and then applies the source projection
normalization.  The final target projection is deliberately omitted so that this
statement is a strict intermediate step of the finite transpose argument.
Source: lem-fix-operation-reduction, compact-support and final paragraphs.
(blueprint: lem-sf-compact-support-realized-scalar-transpose-projection)
-/
theorem sfCompactSupportRealizedScalarTransposeProjection
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    let FX := sfCompactSupportFiniteIntegralFunctor l K₀ hl c E
    let TX := sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι X
    let q := (integralScalarExtension l E L ι Y).map
        ((FrobeniusExchange.compactRealization l E K₀ hl f c).hom.app K) ≫
      (FrobeniusExchange.coefficientExchange l E L ι
        (FrobeniusExchange.systemDerivedOpen l E c.i ⋙ FrobeniusExchange.systemDirect l E c.g)
        (FrobeniusExchange.systemDerivedOpen l L c.i ⋙ FrobeniusExchange.systemDirect l L c.g)
        (FrobeniusExchange.systemCompactScalar l E L ι c)).app K ≫
      (FrobeniusExchange.compactRealization l L K₀ hl f c).inv.app (TX.obj K)
    let R := (proEtaleCoefficientRestrictScalars Y
      (integralScalarQuotientMap l E L ι n)).mapDerivedCategory
    (sfMixedCompletedReductionUnit l E L ι Y n (FX.obj K).obj ≫
        R.map ((scalarReductionDerivedExtension l L Y n).map q ≫
          (sfCompactSupportFiniteReductionIso l K₀ hl c L (TX.obj K) n).hom)) ≫
      R.map ((sfCompactSupportFiniteReductionIso l K₀ hl c L (TX.obj K) n).inv) =
      ((sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom ≫
        (sfAmbientCompactSupportCandidate
          (Padic.coefficientExtensionRing l E (n + 1)) c).map
          (sfMixedCompletedReductionUnit l E L ι X n K.obj) ≫
        (sfCompactSupportRestriction c
          (integralScalarQuotientMap l E L ι n)).hom.app
          ((scalarReductionDerivedExtension l L X n).obj (TX.obj K).obj)) ≫
      R.map ((sfCompactSupportFiniteReductionIso l K₀ hl c L (TX.obj K) n).inv) := by
  sorry

end WeilConjectures
