/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange
public import WeilConjectures.SmoothPurity.RationalWeilPurity.RationalWeilPurityNaturalityMate
import WeilConjectures.SmoothPurity.Frobenius.FrobeniusCompactIntegralAmbientNormalization

/-! # Integral normalization of compact-support Frobenius exchange

Source: the compact-support transport in Step 2 of the current blueprint's
`thm-pur-weil-equivariance-of-purity-and-trace.proof.md`.
(blueprint: lem-pur-frobenius-compact-integral-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The whole-system proper/open exchange agrees, before scalar localization, with
its ordinary completed-coefficient construction.

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
`thm-pur-weil-equivariance-of-purity-and-trace.proof.md`, Step 2; the proper/open
construction in `def-weil-system-operation-exchange-realization` and
`def-zl-frobenius-compact-support-comparison`.
(blueprint: lem-pur-frobenius-compact-integral-normalization).

Proof: use simultaneous K-flat inverse images and K-injective direct images on the
category of the actual quotient-coefficient systems. The normalized inverse-image
composition maps give the same commuting Frobenius square after restricting to
completed coefficients. The comparison with ordinary pullback is
completedToOrdinary, whose normalization is fixed by the completion unit. On a
flat representative its underlying augmentation sends an inverse-image generator
to 1 tensor that generator in every quotient, with zero shifted Roos coordinate.
These maps commute with all quotient transitions. The product projections and the two Roos
coordinates identify the resulting chain maps before derived localization.
Write a right mate as its unit, the pullback square, then its counit. The coefficient
comparison preserves these three factors, since their adjunction transposes are
the same normalized generator maps. Thus the proper-system factor agrees with
the ordinary proper factor. The dual calculation for left mates identifies the
open-system factor with the ordinary open factor. Naturality of the units and
counits and the triangle identities give these equations on the whole quotient
system. Invert the open identity and paste it after the proper identity.
The comparison for their composite is the projection-normalized compact-support
realization: both realization maps have the actual Roos projection adjoints, so
their uniqueness specifications identify them. In the pasted composite the
intermediate realization and its inverse cancel. The resulting outside factors
are completedToOrdinary at the output, ordinary Frobenius of the inverse support
realization, zlCompactSupportFrobenius, the support image of inverse
completedToOrdinary at the input, and the support realization at the completed
pullback. This is exactly integralExchange. Restriction to the full constructible
subcategory retains the same maps and gives the stated heterogeneous equality.
All equations concern whole systems and retain their quotient transitions. For
an empty scheme the maps are the unique zero maps; for an identity factor the
corresponding mate equation is its adjunction triangle identity. -/
theorem frobeniusCompactIntegral_normalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c₀ : Compactification f₀.left)
    (M : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left) :
    HEq ((FrobeniusExchange.frobeniusCompactIntegral D l hl E f₀ c₀).app M)
      (RationalWeilPurity.integralExchange D l hl f₀ E c₀ M).hom         := by
  have h := frobeniusCompactIntegral_ambient_normalization D l hl f₀ E c₀ M
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  exact eq_of_heq h

end WeilConjectures
