/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Residue field of a point of a fibre product

Source: Stacks Project, Schemes, Lemma 26.17.5 (Tag 01JT)
(blueprint: lem-weil-pbc-fibre-product-point-residue-field).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Pullback

/-- Stacks Project, Schemes, Lemma 26.17.5 (Tag 01JT), residue-field assertion
(blueprint: lem-weil-pbc-fibre-product-point-residue-field).
The residue field of the kernel of the canonical tensor map is isomorphic to the residue
field of the point, compatibly with both factor fields. If the tensor quotient is already a
field, its induced map is likewise an isomorphism compatible with both factors.

Proof (the six steps of the node):
1. Naturality of the canonical residue-field points and uniqueness of morphisms from a field
spectrum give equality of the two maps from the base residue field. The tensor universal
property gives `ofPointTensor z`; its kernel is prime.
2. The tensor inclusions and the fibre-product universal property give the map `SpecTensorTo`
from the spectrum of the tensor ring to the fibre product.
3. Composing it with the spectrum of `ofPointTensor z` gives the canonical point morphism,
by equality of both projections and uniqueness in the fibre-product universal property.
4. The field-spectrum residue-field lemma identifies the induced map from the residue field
of the kernel with the unique extension of the tensor quotient injection. It also shows that
`SpecTensorTo` sends this prime to `z`.
5. Naturality of residue-field points and uniqueness of maps from a field spectrum show that
this induced field map composed with the residue-field map of `SpecTensorTo` is the identity.
6. The induced field map is injective since it is a field map and surjective by step 5.
Its extension identity gives compatibility with both inclusions. If the quotient is a field,
its map to its fraction field is an isomorphism, giving the final assertion.
Steps 1--5 use lem-weil-pbc-residue-field-point-naturality,
lem-weil-pbc-morphism-from-spec-field, def-weil-affine-spectrum, def-weil-residue-field,
def-pc-fibre-product, and lem-weil-pbc-spec-field-point-residue-field as recorded in the node.
-/
theorem exists_residueField_equiv_ofPointTensor {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    let T := Triplet.ofPoint z
    let ψ := (ofPointTensor z).hom
    let p := RingHom.ker ψ
    letI : p.IsPrime := RingHom.ker_isPrime ψ
    (∃ e : p.ResidueField ≃+* (pullback f g).residueField z,
      e.toRingHom.comp (algebraMap T.tensor p.ResidueField) = ψ ∧
      e.toRingHom.comp ((algebraMap T.tensor p.ResidueField).comp T.tensorInl.hom) =
        ((pullback.fst f g).residueFieldMap z).hom ∧
      e.toRingHom.comp ((algebraMap T.tensor p.ResidueField).comp T.tensorInr.hom) =
        ((pullback.snd f g).residueFieldMap z).hom) ∧
    (IsField (T.tensor ⧸ p) →
      ∃ e : (T.tensor ⧸ p) ≃+* (pullback f g).residueField z,
        e.toRingHom.comp (Ideal.Quotient.mk p) = ψ ∧
        e.toRingHom.comp ((Ideal.Quotient.mk p).comp T.tensorInl.hom) =
          ((pullback.fst f g).residueFieldMap z).hom ∧
        e.toRingHom.comp ((Ideal.Quotient.mk p).comp T.tensorInr.hom) =
          ((pullback.snd f g).residueFieldMap z).hom) := by
  sorry

end AlgebraicGeometry.Scheme.Pullback
