/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFieldTensorRationalBasicData

/-! # Compatibility part of rational point-field tensor descent

This interface constructs the rational tensor comparison, together with its
normalization equations and scalar squares, over any chosen lift and scalar-extension
construction data.
(blueprint: lem-sf-point-field-tensor-descent-rational-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

/-- The rational tensor comparison with its normalization and scalar-square equations,
over fixed lift and scalar-extension construction data.
(blueprint: lem-sf-point-field-tensor-descent-rational-compatibility).
-/
structure PointFieldTensorRationalCompatibilityData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E)
    (B : PointFieldTensorRationalBasicData D l hl I) where
  rational : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorData D l hl E (I E)
  rational_model : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorCanonical D l hl E
      (I E) (rational E) (B.lift E) (B.localization E)
  rational_unit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorUnitCanonical D l hl E
      (I E) (rational E) (B.lift E) (B.localization E)
  rational_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    PointRationalTensorScalarSquare D l hl E L ι (I E) (I L)
      (rational E) (rational L) (B.field_scalar E L ι)

/-- The normalized rational tensor comparison and its scalar squares exist.
(blueprint: lem-sf-point-field-tensor-descent-rational-compatibility).

Proof source: the rationalization paragraph of the proof of
`lem-sf-point-field-tensor-descent`.  The integral residue-Tor theorem supplies the
finite-Tor hypotheses on the integral models of rational constructible objects.  Define
the rational strong structure by transporting the normalized integral comparison and its
coefficient unit through the balanced localization tensorator of `B` and the size
normalization; since the coefficient/carrier lift of `B` is fully faithful, this fixes a
unique small rational comparison and unit, and the monoidal and symmetry axioms descend
from the integral ones.  Localizing each integral scalar square `hscalar E L ι` along the
field-scalar tensorator of `B` gives the rational scalar square.  The data of `B` are
pinned by their counits and representative models, so the statement holds for every `B`.
-/
theorem pointFieldTensorRationalCompatibility
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E)
    (C : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorCanonical D l hl E (I E))
    (hscalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
      PointIntegralTensorScalarSquare D l hl E L ι (I E) (I L) (C E) (C L))
    (B : PointFieldTensorRationalBasicData D l hl I) :
    Nonempty (PointFieldTensorRationalCompatibilityData D l hl I B) := by
  sorry

end WeilConjectures
