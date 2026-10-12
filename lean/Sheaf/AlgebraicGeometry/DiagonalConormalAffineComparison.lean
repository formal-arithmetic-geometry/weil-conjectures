/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.DiagonalConormalDerivation
import Sheaf.AlgebraicGeometry.AffineConormalSections

/-!
# The diagonal comparison on affine sections

Source: Stacks Project, Tag 08S2, affine calculation; Tag 00RW.
(blueprint: lem-sc-diagonal-conormal-affine-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The morphism induced by a normalized difference derivation is bijective on sections
of an affine open mapping into an affine open of the base.
Source: Stacks Project, Tag 08S2, final affine calculation, and Tag 00RW.
(blueprint: lem-sc-diagonal-conormal-affine-comparison).
Proof: put `A = Γ(X,U)` and `R = Γ(S,V)`, with the algebra structure from `f.appLE`.
The ambient open `U ×_V U` is `Spec(A ⊗_R A)` and its inverse image under the diagonal
is `U` (Tag 01KJ). Restriction of the actual kernel sheaf to this open is the ideal of
that closed immersion, namely the kernel of multiplication. Tensor pullback commutes
with these restrictions, so the canonical affine conormal sections equivalence of
Tag 01R3 identifies sections of `diagonalConormal f` over `U` with `I/I²`, including
its class-map formula. The restriction, base-open and affine isomorphisms for relative
differentials identify its sections with `Ω[A/R]` and its universal derivation with `D`.
The normalization hypothesis and the universal-property evaluation formula imply that
our morphism sends `da` to the class of `1 ⊗ a - a ⊗ 1`. These elements generate
`Ω[A/R]`, so the whole map is the canonical identification of Tag 00RW. In Mathlib,
`KaehlerDifferential R A` is exactly the cotangent of the multiplication ideal, and
`KaehlerDifferential.D_apply` gives this formula. Conjugating this linear equivalence
by the two section identifications proves bijectivity. This argument needs only this
affine chart, and makes no claim about gluing or about global invertibility. -/
theorem diagonalConormalComparison_bijective_on_affine (f : X ⟶ S)
    (D : (diagonalConormal f).val.Derivation' f.pullbackPresheafToPresheaf)
    (hD : IsDiagonalConormalDerivation f D) (U : X.affineOpens) (V : S.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    Function.Bijective (((f.relativeDifferentialsHomEquiv (diagonalConormal f)).symm D).app
      U.1) := by sorry

end AlgebraicGeometry
