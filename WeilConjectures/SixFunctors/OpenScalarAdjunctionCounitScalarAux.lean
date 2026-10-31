/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.OpenScalarExchange
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsSupplement

/-! The unbounded scalar/open counit component of the locally closed coefficient argument.

Source: Weil blueprint, `lem-coef-finite-closed-shriek`, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit-scalar-aux).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefOpenCounit

/-- The normalized scalar/open counit equation on the whole unbounded derived category.

The proof is the mate calculation for the two normalized scalar adjunctions and the
open adjunction.  The scalar comparison is characterized by the common right-adjoint
identification, while the inverse tensor comparison is characterized by the open unit.
Pasting the adjunct-counit identity with the naturality squares and cancelling the
comparison isomorphism reduces the equation to the triangle identity for the A-open
adjunction.  This argument is carried out on arbitrary derived objects and does not
use flatness of the coefficient map.
Source: Weil blueprint, `lem-coef-finite-closed-shriek`, proof paragraph 3
(blueprint: lem-coef-open-scalar-adjunction-counit-scalar-aux). -/
theorem scalar_counit_aux
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] :
    ∀ M : _root_.DerivedCategory
        (proEtaleRingModules X (proEtaleConstantRing X A)),
      (openScalarIso φ j).hom.app ((constantPullback (A := A) j).obj M) ≫
          (openExtension (A := B) j).map ((tensorPullbackIso φ j).inv.app M) ≫
          (proEtaleRingDerivedOpenAdjunction j
            (proEtaleConstantRing X B) (proEtaleConstantRing V B)
            (proEtaleConstantRingComparison j B)).counit.app
            ((scalarExtension φ X).obj M) =
        (scalarExtension φ X).map ((proEtaleRingDerivedOpenAdjunction j
          (proEtaleConstantRing X A) (proEtaleConstantRing V A)
          (proEtaleConstantRingComparison j A)).counit.app M) := by
  sorry

end AlgebraicGeometry.ProEtale.CoefOpenCounit
