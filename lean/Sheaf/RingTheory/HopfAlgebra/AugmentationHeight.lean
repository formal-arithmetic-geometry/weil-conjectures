/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Height
import Sheaf.RingTheory.IntegralExtensionDimension
import Sheaf.RingTheory.KrullDimension.GoingDown

/-!
# The augmentation ideal has the dimension of a finite type group

Source: blueprint `lem-wf-same-lie-closed-subgroup`, proof, Dimension paragraph:
translations identify all closed-point local dimensions, and their maximum is the
global dimension. This argument is independent of smoothness and characteristic.
(blueprint: lem-wf-hopf-augmentation-height).
-/

@[expose] public section

namespace HopfAlgebra

/-- The local dimension at the identity of a finite type affine group scheme equals
its global dimension, even for a nonreduced group scheme in positive characteristic.

Source: `lem-wf-same-lie-closed-subgroup`, proof, Dimension paragraph (the translation
and maximum argument), extended to arbitrary fields by algebraic closure.

Proof in words: first suppose `k` is algebraically closed. Every maximal ideal is the
kernel of a `k`-point, by the weak Nullstellensatz for finite type algebras. For a point
`g`, convolution with `g` defines a translation automorphism; convolution with its
inverse is the inverse automorphism, and the counit identities show that it carries
the identity point to `g`. The induced local ring isomorphism shows that the height
of `ker g` is the height of the augmentation ideal. The Krull dimension of a
nontrivial ring is the supremum of the heights of its maximal ideals. Consequently
it equals this common height. Nontriviality follows from the counit onto the field.

For general `k`, let `K` be its algebraic closure and put `B = K ⊗[k] A`, with its
base-changed Hopf structure. The map `A → B` is faithfully flat and integral: `K/k`
is algebraic, so every finite subset of `B` is contained in the base change by a
finite extension. Thus going-up, incomparability and lying-over identify the global
Krull dimensions of `A` and `B`. The augmentation ideal of `B` contracts to that of
`A`, and its fibre is `K ⊗[k] (A/ker ε) = K`. The local flat dimension formula for
Noetherian local rings therefore gives equal local dimensions at these two
augmentation ideals (the fibre is a field of dimension zero). These local dimensions
are their heights. Apply the algebraically closed case to `B` and substitute both
equalities. No reducedness, regularity or characteristic assumption is used.
(blueprint: lem-wf-hopf-augmentation-height). -/
theorem height_ker_counit_eq_ringKrullDim
    (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] :
    ((RingHom.ker (Bialgebra.counitAlgHom k A)).height : WithBot ℕ∞) =
      ringKrullDim A := by sorry

end HopfAlgebra
