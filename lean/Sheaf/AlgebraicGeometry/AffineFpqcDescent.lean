/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.FpqcDescendingTypesMorphisms
import WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra

/-!
# Effective fpqc descent of affine morphisms

Source: Stacks Project, Descent, Lemma 35.37.1 (Tag 0245)
(blueprint: lem-galois-fpqc-affine-descent-effective).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.Over.DescentDatum

/-- For the singleton fpqc covering `p : X ⟶ Y`, a descent datum on an affine
`X`-scheme is effective (Stacks Project, Descent, Lemma 35.37.1, Tag 0245).

The node's proof proceeds as follows:
1. Affine morphisms remain affine under base change
   (`lem-weil-pbc-affine-morphism-permanence`).
2. Finite coproducts of affine morphisms are affine, by decomposing each
   affine open into clopen affine pieces (`lem-weil-pbc-scheme-coproduct-family`,
   `lem-weil-pbc-spec-clopen-idempotent`).
3. The fpqc reduction (`lem-galois-fpqc-descending-types-morphisms`) leaves
   a flat surjective morphism of affine schemes; express all objects as spectra.
4. The descent isomorphism becomes an algebra isomorphism over the tensor
   square; its cocycle becomes the corresponding threefold tensor identity.
5. The induced coaction is coassociative by that identity and counital by
   restricting the cocycle to the diagonal.
6. Flat algebra descent (`lem-galois-flat-algebra-descent`) gives the invariant
   algebra and its base-change isomorphism.
7. Its spectrum is the descended scheme; checking the isomorphism on invariant
   algebra generators proves compatibility with the datum.
8. Apply `lem-galois-fpqc-descending-types-morphisms` to the original covering.

(blueprint: lem-galois-fpqc-affine-descent-effective) -/
theorem isEffective_of_isAffineHom_fpqc {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y) {V : Over X}
    [IsAffineHom V.hom] (D : Over.DescentDatum p V) : D.IsEffective := by
  sorry

end CategoryTheory.Over.DescentDatum
