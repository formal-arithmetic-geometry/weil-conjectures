/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullback

/-! # A step of diagonal scalar pullback propagation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Invertibility of the canonical ordinary supported-source map for the diagonal.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), closed diagonal base change.
(blueprint: lem-diagonal-scalar-closed-source-exchange).

Proof: The diagonal square is Cartesian by projective-space base change and the
universal property of the self-product. The inverse image of a closed direct image
vanishes on the primed open complement, since inverse-image composition identifies
its restriction with inverse image of the unprimed complementary restriction.
Closed-support localization makes the primed closed adjunction unit invertible.
The closed counit is invertible by full faithfulness. Expanding the exchange mate
as this unit, the inverse-image comparison and this counit therefore proves it
invertible. The pseudonatural forgetful comparisons preserve the square, unit and
counit and reflect invertibility, so the same holds for condensed module objects.
Compose with direct image of c.iso; its composite is sourcePullbackMap by definition.
This argument includes the empty scheme and does not use coefficients or a trace. -/
theorem diagonalScalar_source_map_isIso
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (b : BaseSquares g) (c : UnitPullEndpoint R (baseP g)) :
    IsIso (sourcePullbackMap R g b.diagonal_square c) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
