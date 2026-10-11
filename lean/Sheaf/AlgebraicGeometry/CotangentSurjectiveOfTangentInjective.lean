/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.AlgebraicGeometry.SchemeTangentSpace
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Injectivity of the differential implies surjectivity on cotangent spaces

Source: Stacks Project, Tags 0B2E and 0B2F
(blueprint: lem-sc-point-tangent-cotangent-surjective).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a locally finite type morphism over a field, at closed rational points, injectivity
of the differential implies surjectivity on cotangent spaces: the map
`IsLocalRing.CotangentSpace` of the stalk at `f x` to that of the stalk at `x` induced by the
local ring map `f.stalkMap x` (Mathlib's `Ideal.mapCotangent`) is surjective.
The existential in `hdf` supplies the residue-field identification needed by the canonical
`schemeTangentMap`; rationality already implies this identification exists.

Source: Stacks Project, Tags 0B2E and 0B2F
(blueprint: lem-sc-point-tangent-cotangent-surjective).
Proof: First apply `lem-sc-rational-tangent-cotangent-duality` at the two rational points.
Its canonical identifications identify the differential with the dual of the map on maximal
ideals modulo their squares induced by `f.stalkMap x`. Next apply
`lem-sc-dual-map-injective-iff-surjective` to this linear map: injectivity of its dual implies
its surjectivity, which is the claim. -/
theorem cotangent_surjective_of_tangent_injective
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ pY = pX) (x : X)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({f x} : Set Y))
    (hκx : Function.Bijective (pX.residueFieldMap x).hom)
    (hκy : Function.Bijective (pY.residueFieldMap (f x)).hom)
    (hdf : ∃ he : Function.Bijective (f.residueFieldMap x).hom,
      Function.Injective (schemeTangentMap k X Y pX pY f hf x he)) :
    Function.Surjective
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (f.stalkMap x).hom.toIntAlgHom
        (Ideal.map_le_iff_le_comap.mp
          (IsLocalRing.map_maximalIdeal_le (f.stalkMap x).hom)) :
        IsLocalRing.CotangentSpace (Y.presheaf.stalk (f x)) →ₗ[ℤ]
          IsLocalRing.CotangentSpace (X.presheaf.stalk x)) := by
  sorry

end AlgebraicGeometry
