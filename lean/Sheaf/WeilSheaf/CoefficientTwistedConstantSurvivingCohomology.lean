/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.WeilSheaf.CanonicalCoefficientWeilCohomology

/-! # Surviving cohomology of the coefficient shifted Tate constant -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius

attribute [local instance 1100] CategoryTheory.instOverClass

namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

local instance tateSurvivingStructureOver : X₀.hom.IsOver (Spec (.of P.field.k₀)) := by
  constructor
  dsimp only [autoParam]
  change X₀.hom ≫ 𝟙 _ = X₀.hom
  rw [Category.comp_id]

/-- The surviving cohomology of the canonical coefficient shifted Tate constant
is the unshifted coefficient root line, with its actual Weil structure.

Source: BBD 1.3, standard truncations; current blueprint,
lem-pur-constant-purity-frobenius-square, canonicalSourceTheta and its even shift.
(blueprint: lem-sf-coefficient-twisted-constant-surviving-cohomology)

Proof: sourceUnit replaces pullback of the point constant by the scalar unit at the
source. Identify the regular coefficient unit with the reconstructed tensor unit,
using the normalized completed unit map, and apply the tensor right unitor. The
finite-stage inclusion shift comparison identifies the carrier with the root line
shifted by 2d. The root line is in the standard heart by commonWeilLine_heart. Hence
truncation at -2d followed by the -2d shift recovers the unshifted root line.
To check the Weil structure, substitute the conjugation formula canonicalSourceTheta.
The completed unit's Frobenius compatibility and right-unitor naturality cancel its
unit factor. The finite-stage signed Roos normalization retained by
canonicalCoefficientWeilCohomology identifies the shift comparison on this root line
with the one in shiftedLineTheta. The normalized truncation-unit and counit equations
then leave precisely commonDerivedLineMap. Thus the carrier isomorphism intertwines
Frobenius and lifts to the full coefficient Weil heart. At d=0 the shift is zero
and the root line is the unit; empty schemes give the unique zero-object comparison. -/
theorem coefficient_twisted_constant_surviving_cohomology (d : ℕ) :
    Nonempty ((canonicalCoefficientWeilCohomology P X₀ (-2 * (d : ℤ))).obj
        (twistedConstant P X₀ d) ≅
      FrobeniusCoefficientTwists.commonWeilSheaf P.field P.coefficients.l
        P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)) := by sorry

end WeilConjectures.NativeCoefficientCohomology
