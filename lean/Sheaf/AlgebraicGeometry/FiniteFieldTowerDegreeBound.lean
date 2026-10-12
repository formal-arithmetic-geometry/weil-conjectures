/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.RingTheory.NakayamaNilpotent

/-!
# Degree estimate for a tower finite over a field

Source: Stacks Project, Morphisms, proof of Tag 03J6, algebraic dimension estimate.
(blueprint: lem-weil-pbc-finite-field-tower-degree-bound).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The degree of a finite tower over a field is bounded using the fibre degrees
of its first map.

Source: Stacks Project, Morphisms, proof of Tag 03J6, the argument after writing
`X_z = Spec A` and `Y_z = Spec B`.
(blueprint: lem-weil-pbc-finite-field-tower-degree-bound)

Proof: Both schemes are affine because their structure morphisms are finite. Put
`B = Γ(Y, ⊤)` and `A = Γ(X, ⊤)`, with the compatible algebra structures induced by
`g` and `f`. Decompose the Artinian algebra `B` into its local factors `B_i`.
The affine pullback formula identifies the fibre at the corresponding point with
`Spec (A_i / m_i A_i)`, where `A_i = A ⊗[B] B_i` and `m_i` is the maximal ideal
of `B_i`. Its residue-field dimension is at most `n` by the hypothesis. Lift a basis
of that quotient to `A_i`. Since `m_i` is nilpotent, Nakayama gives a surjection
from at most `n` copies of `B_i` onto `A_i`. Restrict scalars to `K` and compare
dimensions. Summing over the finite set of factors gives the claimed inequality.
The empty target corresponds to the zero ring and empty product, giving `0 ≤ 0`.
For `n = 0`, Nakayama makes every `A_i` zero, so the estimate still holds. -/
theorem finrankΓ_comp_le_mul_of_finite {X Y : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) [IsFinite f] [IsFinite g] (n : ℕ)
    (hf : ∀ y, (f.fiberToSpecResidueField y).finrankΓ ≤ n) :
    (f ≫ g).finrankΓ ≤ n * g.finrankΓ := by sorry

end AlgebraicGeometry.Scheme.Hom
