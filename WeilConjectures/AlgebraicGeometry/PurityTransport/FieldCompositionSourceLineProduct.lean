/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceGeometricData

/-! # Scalar compatibility of a normalized shifted Tate comparison

Source: smooth composition's coefficient passage, root and power calculation.
(blueprint: lem-pur-field-composition-source-line-product). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Scheme
open CategoryTheory.Functor.OplaxMonoidal
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
attribute [local irreducible] DerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

/-- Scalar extension preserves the normalized shifted Tate multiplication.
Source: smooth composition's coefficient passage, product part of Step 2.
(blueprint: lem-pur-field-composition-source-line-product).

Proof in words. Choose the ordinary scalar monoidal structure fixed by its
balanced-pairing normalization. The power_normalized equations identify Px.power
with powerPull of Px.first for this same structure. Induct on the second
exponent of lineProduct. At zero use the right unitor and scalar unit; at a
successor use inverse associativity and inverse-tensorator naturality. This
proves ordinary multiplicativity of the coordinate maps. Under the derived
scalar adjunction, scalarLineZero is the transpose of the single of the
ordinary adjunct. Compare the derived unit on a single complex with the
single of the ordinary unit, and cancel the exact restriction comparison;
this identifies scalarLineZero with the canonical single comparison followed
by single(Px.power). Tate lines are flat, so the singleTensor comparisons are
computed on flat complexes in degree zero and the derived scalar tensorator
has the same multiplicative square. Finally transport this square through the
two adjunction-shift maps and shiftTensorShiftIso. Their compatibility is checked
on the shifted single complexes, and the shift-addition equality is exactly
2(d+e)=2d+2e. Scalar extension preserves the Koszul braiding; both shifts are
even. Invert the multiplication square and then apply that braiding square to
obtain the displayed equation. This also covers either exponent zero and ell=2. -/
theorem fieldCompositionSourceLineProduct
    (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (hunit : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    (X : Scheme.{u}) [∀ x : X, Invertible (ell : X.residueField x)]
    [PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom X))]
    (Px : ScalarLineCoordinates ell a hunit X) (d e : ℕ) :
    letI := fieldCompScalarMonoidal ell a X
    letI := _root_.DerivedCategory.braidedCategory'
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj ell) X))
    letI := _root_.DerivedCategory.braidedCategory'
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c'.obj ell) X))
    (scalarSixChange a X).map
        (((derivedProduct ell c X d e).symm ≪≫ β_ _ _).hom) ≫
      δ (scalarSixChange a X) (c.derivedLine ell X e) (c.derivedLine ell X d) ≫
        (scalarLineMap ell a X e (Px.power e) ⊗ₘ
          scalarLineMap ell a X d (Px.power d)) =
      scalarLineMap ell a X (d + e) (Px.power (d + e)) ≫
        (((derivedProduct ell c' X d e).symm ≪≫ β_ _ _).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
