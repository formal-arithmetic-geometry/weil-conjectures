/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite
import Sheaf.AlgebraicGeometry.IrreducibleProductOverField
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism

/-!
# The neutral component of a group locally of finite type over a field

Source: Stacks Project, groupoids.tex, Tag 0B7R (proposition-connected-component),
and topology.tex, Tags 04MF and 04ME
(blueprint: lem-sfb-lft-field-group-neutral-component).

The component has its open-subscheme structure, retaining all nilpotents. Equality after
field extension is expressed as equality of the corresponding open subsets of the pullback;
both open subschemes carry the restriction of its structure sheaf to that subset.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- Over any field, the identity component of a group scheme locally of finite type is
clopen, a finite-type geometrically irreducible open subgroup, and commutes with every
field extension. The group structure is on the open subscheme itself.

Source: Stacks Project, groupoids.tex, Tag 0B7R (proposition-connected-component),
and topology.tex, Tags 04MF and 04ME
(blueprint: lem-sfb-lft-field-group-neutral-component).

Proof:
1. The field is Noetherian (pqf-def-locnoeth). Local finite type then makes G locally
   Noetherian (pqf-lem-locnoeth-lft), so its irreducible components are locally finite by
   lem-sc-locnoeth-components-locally-finite. No quasi-compactness of G is needed.
2. By lem-sfb-group-local-minimal-prime each local ring has a unique minimal prime.
   The prime correspondence of lem-weil-pbc-primes-of-localization and the component
   description of lem-weil-pbc-spec-irreducible-components-minimal-primes show that
   exactly one affine irreducible component passes through each point. By
   lem-sc-components-open-injection and lem-sc-irreducible-components-cover the same
   holds in G. Thus distinct components are disjoint.
3. Let Z be the component containing the identity. At a point of Z remove the finitely
   many other closed components meeting a small neighbourhood. The remaining open
   neighbourhood lies in Z, so Z is clopen (def-weil-irreducible-components). Since Z is
   irreducible it is connected, and the clopen separation implies Z is exactly the
   connected component C (def-weil-connected-scheme). Its open structure reduces to the
   reduced induced structure of Z (def-weil-pbc-scheme-reduction), geometrically
   irreducible by lem-sfb-group-local-minimal-prime. The universal homeomorphism in
   lem-weil-pbc-reduction-universal-homeomorphism transports this property to C itself
   (def-pc-geometrically-irreducible), without deleting its nilpotents.
4. By lem-weil-pbc-open-fibre-product the product of C with itself is open in the product
   of G with itself. It is irreducible by lem-sc-irreducible-product-over-field. Its
   multiplication image is connected and contains the identity, hence lies in C.
   Inversion also preserves C and the unit lands there. Factor these maps through the
   open immersion using lem-weil-pbc-morphism-factors-through-open-subscheme. Uniqueness
   of factorization makes the group diagrams commute (def-sc-group-scheme).
5. By lem-sfb-irreducible-group-quasi-compact this irreducible group C is quasi-compact.
   It is locally of finite type: refine affine finite-type charts of G by principal
   opens contained in C. Their algebras are still finitely generated. Thus C is of
   finite type (def-weil-finite-type-morphism).
6. For any extension K/k, pull back the clopen decomposition C and its complement.
   By lem-weil-pbc-open-immersion-base-change and lem-weil-pbc-open-fibre-product their
   images are the inverse images under the projection G_K to G. Geometric
   irreducibility makes C_K nonempty and connected, and the base-changed identity
   lands in it (def-pc-base-change). Thus C_K lies in the identity component of G_K.
   Conversely that component cannot cross the clopen decomposition, so it lies in
   C_K. Both have the restriction of the structure sheaf to this same open subset,
   proving equality as open subschemes (def-weil-open-immersion). -/
theorem lftFieldGroup_neutralComponent
    (k : Type u) [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] :
    ∃ U : G.left.Opens,
      (U : Set G.left) = connectedComponent (GrpObj.onePoint G) ∧
      IsClosed (U : Set G.left) ∧
      GeometricallyIrreducible (U.ι ≫ G.hom) ∧
      LocallyOfFiniteType (U.ι ≫ G.hom) ∧ QuasiCompact (U.ι ≫ G.hom) ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹'
          (U : Set G.left) =
        connectedComponent (GrpObj.onePoint
          ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G))) ∧
      ∃ gC : GrpObj (Over.mk (U.ι ≫ G.hom)),
        @IsMonHom _ _ _ _ _ gC.toMonObj _ (Over.homMk (V := G) U.ι) := by
  sorry

end AlgebraicGeometry
