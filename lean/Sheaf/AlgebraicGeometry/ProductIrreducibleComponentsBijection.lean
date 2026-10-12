/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Over
import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Irreducible components of a product over a field

Source: Stacks Project, Varieties, Lemma 33.8.4, Tag 038F
(blueprint: lem-sc-product-irreducible-components-bijection).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The projection from a product with a geometrically irreducible scheme over a field induces
 a bijection on irreducible components (Stacks Project, Varieties, Tag 038F).
(blueprint: lem-sc-product-irreducible-components-bijection)

Proof: Write `p` for the second projection. It is open because it is the base change of the
structure morphism of `U`, which is universally open over a field
(`lem-sc-scheme-over-field-universally-open`, `def-pc-base-change`, `def-pc-fibre-product`).
For every point `y` of `V`, pasting the fibre-product squares identifies the scheme-theoretic
fibre with the base change of `U` to the residue field of `y` (`def-weil-residue-field`,
`def-pc-field-extension`, `def-pc-fibre-product`). This is irreducible by geometric
irreducibility (`def-pc-geometrically-irreducible`), and its underlying space is homeomorphic
to the set-theoretic fibre (`def-pc-scheme-fibre`). Thus the fibres of `p` are irreducible.
Apply `lem-sc-open-map-irreducible-fibres-components` (Stacks Tag 037A): inverse image sends
components of `V` bijectively to components of the product, with inverse given by image under
`p` (`def-weil-irreducible-components`). -/
theorem product_irreducibleComponents_bijOn_image
    (K : Type u) [Field K] (U V : Scheme.{u})
    [U.Over (Spec (CommRingCat.of K))] [V.Over (Spec (CommRingCat.of K))]
    [GeometricallyIrreducible (U ↘ Spec (CommRingCat.of K))] :
    let f := U ↘ Spec (CommRingCat.of K)
    let g := V ↘ Spec (CommRingCat.of K)
    Set.BijOn (Set.image (pullback.snd f g))
      (irreducibleComponents ↥(pullback f g)) (irreducibleComponents V) := by
  sorry

end AlgebraicGeometry
