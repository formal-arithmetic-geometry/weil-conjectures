/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.Paper.FiniteProjectionFixedCoordinates

/-! # Direct counit in fixed coefficients

Source: the proper-factor calculation of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportFiniteProjection

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- The direct adjunction counit in the two fixed coefficient coordinates.
There are no tensor products, properness assumptions, or projection maps in this identity.
Source: def-sf-operation-stages, finiteDirectAdjunctionNormalization; the normalized
coefficient adjunction of def-weil-proetale-inverse-image.
(blueprint: lem-sf-finite-direct-counit-fixed-realization).

Proof: take the adjunction comparison supplied by finiteDirectAdjunctionNormalization
and substitute its prescribed left and right comparisons into its counit equation.
Apply the inverse coefficient realization. The intrinsic constant-module adjunction
is the underived fixed-scalar adjunction conjugated by the section-normalized
coefficient equivalence. Its derived adjunction uses the same comparison on K-injective
representatives. The published sfIntrinsicDerivedDirectImageComparison is determined
by exactly those representatives, so it identifies this derived right comparison with
the one in directCoordinates. The left comparison is mapDerivedCategoryCompIso followed
by cancellation of the coefficient unit; the K-flat/exact comparison identifies its
adjunction with fixedAdjunction. Naturality of the coefficient units and counits and
their triangle identities give the displayed equation. This computation applies to
all bounded constructible inputs, including zero, and to every morphism. -/
theorem directCounit_fixed_realization (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (K : sixFunctorFiniteCategory D C E n hn X) :
    (fixedPullRealization S f ((S.finite.direct f).obj K)).hom ≫
      (fixedDerivedPull (C := C) (E := E) (n := n) f).map
        (directCoordinates S f K).hom ≫
      (fixedAdjunction (C := C) (E := E) (n := n) f).counit.app
        ((coordinates (C := C) (E := E) (n := n) (hn := hn) X).obj K) =
    (coordinates (C := C) (E := E) (n := n) (hn := hn) X).map
      ((S.finite.pullDirectAdjunction f).counit.app K) := by
  sorry

end WeilConjectures.CompactSupportFiniteProjection
