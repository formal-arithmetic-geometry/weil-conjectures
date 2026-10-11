/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.RingTheory.HenselianTerminology

/-!
# Sections over a strictly henselian local open and geometric stalks

Source: Stacks Project, Lemma 59.55.1 (Tag 03QO), applied inside an open subscheme
(blueprint: lem-weil-pbc-sets-strictly-henselian-open-sections-stalk).
-/

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- For a sheaf of sets on `T`, the germ map from sections over a strictly henselian
local open `U` to the geometric stalk at its closed point is bijective.
Source: Stacks Project, Lemma 59.55.1 (Tag 03QO)
(blueprint: lem-weil-pbc-sets-strictly-henselian-open-sections-stalk).

Proof:
1. Represent a germ over a pointed etale neighbourhood `V`. Shrink around its marked
point to an affine open contained in the inverse image of `U`, using
`lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink`. This gives an etale algebra
`R → A` and a prime above the maximal ideal of `R`.
2. The residue extension is finite separable by
`lem-weil-pbc-etale-algebra-residue-field-separable`, and is trivial by
`lem-pc-sepclosed-finite-sep-trivial`. The root-lifting criterion
`lem-weil-pbc-henselian-local-root-lifting` and the retraction lemma
`lem-weil-pbc-root-lifting-etale-retraction` give an algebra retraction `A → R`.
Its spectrum yields a section `U → V` over `T` through the marked geometric point:
the residue-field maps agree because the retraction inverts the residue isomorphism.
3. Pointed etale neighbourhoods are cofiltered by
`lem-weil-pbc-pointed-etale-neighbourhoods-cofiltered`. The full subcategory consisting
of `(U, t)` has only its identity endomorphism, since `U.ι` is a monomorphism, and
maps to every neighbourhood by step 2. Apply
`lem-weil-pbc-colimit-initial-full-subcategory` and
`lem-weil-pbc-colimit-constant-connected-diagram` to compute the stalk as `G(U)`.
The colimit coprojection is precisely the germ map written below. -/
theorem strictlyHenselianOpen_toPresheafFiber_bijective
    {T : Scheme.{u}} (U : T.Opens) {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R) (e : U.toScheme ≅ Spec (.of R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (t : Spec (.of Ω) ⟶ U.toScheme) (ht : t ≫ U.ι = s)
    (hclosed : (t ≫ e.hom) default = IsLocalRing.closedPoint R)
    (G : Sheaf (smallEtaleTopology T) (Type (max u v))) :
    Function.Bijective
      ((pointSmallEtale s).toPresheafFiber (Etale.mk U.ι) (Over.homMk t ht) G.obj) := by
  sorry

end AlgebraicGeometry.Scheme
