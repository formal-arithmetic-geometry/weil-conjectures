/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S7
-/
module

public import Sheaf.Topology.ProfiniteIntegralScalarDefinitions

/-! # The continuous scalar comparison

Source: HRS Example 3.1 and Remark 3.2, with the argument in
`lem-sfb-profinite-integral-scalar-realization`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct CategoryTheory.Obj

namespace Profinite.IntegralScalar

/-- Cover-local lifting of generators and relations gives the normalized ordinary
scalar extension comparison.

Source: HRS Example 3.1 and Remark 3.2; steps 4--6 of
`lem-sfb-profinite-integral-scalar-realization`.
(blueprint: lem-sfb-integral-continuous-scalar-comparison)

Proof: Constant functions define the scalar ring map φ and its multiplicative structure.
The constant sheaf on B, with its sheafified ordinary O-action, has ConstantCoordinates.
Continuous B-valued functions, with precomposition and pointwise multiplication, form
an internal module with ContinuousCoordinates. The extension-restriction adjunction
and the tensor universal property identify scalar extension with sheafification of
Q ↦ C(Q,O) ⊗_O B. The comparison sends f tensor b to q ↦ f(q) • b.
For a finite presentation O^m → O^n → B and a continuous section b on Q, pull back the
profinite surjection O^n → B. This cover lifts b to coordinates, proving local
surjectivity. For a tensor relation, its coordinates lie in the closed relation module
N. Pull back O^m → N to lift it on a profinite cover; there it is an actual presentation
relation, proving local injectivity. Sheafification of this locally bijective map is
an isomorphism. Its inverse is linear since the comparison is linear and invertible.
The formula on 1 tensor b gives the required normalization. The zero presentation and
empty site objects use empty sums and unique empty functions.
-/
theorem continuous_scalar_comparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    letI := spectralNorm.normedField (Padic l) E
    let O := Padic.coefficientExtensionIntegers l E
    let π := Padic.coefficientExtensionUniformizer l E
    TopologyStatement O π → ∀ P : Profinite.{u}, ScalarComparison P O := by sorry

end Profinite.IntegralScalar
