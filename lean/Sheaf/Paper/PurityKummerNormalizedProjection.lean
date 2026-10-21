/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.PurityFiniteKummerDefinitions

/-! # The normalized finite projection comparison

Source: finite Kummer-level blueprint, proof steps 3--4; Stacks Tag 03PK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The root projection induces an isomorphism after the two prescribed scalar extensions.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-purity-conv/lem-pur-finite-kummer-level.proof.md, steps 3--4; Stacks Tag 03PK.
(blueprint: lem-pur-kummer-normalized-projection)

Proof: put L=lim_r mu_(ell^(r+1)). Its projection to level N+1 has kernel
ell^(N+1)L: for a compatible sequence with zero N-th coordinate, shift its
coordinates by N+1 and regard the shifted roots as roots of the smaller order.
This gives a compatible sequence whose ell^(N+1) multiple is the original one.
The reverse inclusion follows because that coordinate is killed by ell^(N+1).
Balanced tensor relations identify scalar reduction of L with its quotient by
these multiples. Thus its induced map to the finite root sheaf is mono. Both
are locally free rank-one lines by the Tate-line local-model theorem. On a common
trivializing cover the map is multiplication by a locally constant scalar.
On each nonempty cover member a nonunit scalar is divisible by ell and kills the
nonzero section ell^N, contradicting monicity. On an empty member both sheaves
are zero. Therefore the map is invertible. Finally associate the two integral
scalar extensions and factor the coefficient action through Z/ell^(N+1).
The forward tensor formula sends z tensor (b tensor x) to
(z times the image of b) tensor the N-th coordinate of x. The inverse is given
by the inverse finite root comparison and the inverse associator. Tensor
relations and the two sheafification universal properties prove the formula.
This construction uses no basis of the finite coefficient module. -/
theorem kummer_normalized_projection (P : PurityFiniteSetting.{u})
    (n N : ℕ)
    (hI : Padic.coefficientExtensionIdeal P.coefficients.l P.extension (n + 1) =
      Ideal.span {((P.coefficients.l : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension) ^ (N + 1))})
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+* P.kummerCoefficient n)
    (T : Scheme.{u}) (hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)) :
    ∃ α : P.kummerLine n T ≅ P.kummerRootsTensor n N a T,
      P.IsKummerComparison n N a T α := by
  sorry

end WeilConjectures.PurityFiniteSetting
