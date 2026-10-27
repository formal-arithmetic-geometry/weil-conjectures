/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.Topology.Connected.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.Fiber

/-! # Topology of an algebraic-space fibre over a scheme point

Source: Stacks Project, Decent Spaces, Tag 0AC8, lemma-topology-fibre, specialized
to a scheme target; Schemes, Tag 01K1; Properties of Spaces, Tags 03BU and 03H4
(blueprint: lem-sfb-space-scheme-fibre-topology).

On schemes over `T`, the sheaf represented by `T` is terminal. Thus the product of
`X` with the representable presheaf of `Spec κ(t)` is the sheaf fibre product over `T`.
Presheaf products of sheaves are sheaves, and their underlying presheaves agree with
sheaf products. We use this existing product construction without choosing a new model.

The inverse-image subset is written using field-valued representatives: a point belongs
exactly when it has a representative whose unique scheme point maps to `t`. This is
`|f|⁻¹({t})` for the structural map `f : X → T`. Its subtype has the subspace topology.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The projection from the residue-field fibre identifies its point space homeomorphically
with the inverse image of the base point. Preconnectedness and nonemptiness are preserved;
together these also give the equivalence of `ConnectedSpace` on the two spaces.
Source: Stacks Project, Tag 0AC8, lemma-topology-fibre, for a scheme target;
Tags 01K1, 01J9, 03BU and 03H4
(blueprint: lem-sfb-space-scheme-fibre-topology).

Proof:
1. Choose the affine scheme atlas `p : U → X` of lem-a1-space-affine-etale-cover.
   By lem-trf-space-fibre-products-etale-covers its base change is an atlas
   `q : U_t → X_t`, where `U_t = U ×_T Spec κ(t)`. The point maps of `p` and `q`
   are continuous, open and surjective by lem-a1-space-point-open-calculus.
   The scheme fibre homeomorphism of def-pc-scheme-fibre identifies `|U_t|` with
   the subspace of `|U|` lying over `t`, compatibly with the two projections.
2. The fibre-product point-image formula of lem-a1-space-point-open-calculus makes
   the projection onto `|f|⁻¹({t})` surjective. If two fibre representatives have the
   same image in `X`, def-a1-algebraic-space-point-classes gives a common field on
   which their `X` components agree. By lem-weil-pbc-morphism-from-spec-field,
   the map of that field spectrum to `Spec κ(t)` over `T` is uniquely determined
   by its map to `T`. The two fibre representatives therefore agree there too.
   This proves injectivity. Point-open calculus gives continuity of the projection.
3. If `A` is open in `|X_t|`, its inverse image under `q` is open in `|U_t|`.
   By step 1 it is `O ∩ |p|⁻¹(|f|⁻¹({t}))` for an open `O` in `|U|`.
   Commutativity and step 2 identify its image with `|p|(O) ∩ |f|⁻¹({t})`.
   Since `p` is open and both atlases are surjective, the fibre projection is open
   onto the subspace. Its continuous bijective corestriction is a homeomorphism.
4. The displayed representative equation identifies this homeomorphism with the
   first product projection. Transport open decompositions and points along it
   to obtain the preconnectedness and nonemptiness equivalences. This includes
   the empty fibre, a non-locally-closed base point and a non-quasi-compact atlas. -/
theorem schemeFibre_point_homeomorphism {T : Scheme.{u}} (X : AlgebraicSpace T) (t : T) :
    ∃ e : Point (X.obj.obj ⨯ yoneda.obj (Over.mk (T.fromSpecResidueField t))) ≃ₜ
        {x : Point X.obj.obj | ∃ p : PointRepresentative X.obj.obj,
          Quot.mk _ p = x ∧ p.base (IsLocalRing.closedPoint p.K) = t},
      (∀ p : PointRepresentative
          (X.obj.obj ⨯ yoneda.obj (Over.mk (T.fromSpecResidueField t))),
        (e (Quot.mk _ p)).val = Quot.mk _ (p.map
          (prod.fst (X := X.obj.obj)
            (Y := yoneda.obj (Over.mk (T.fromSpecResidueField t)))))) ∧
      (PreconnectedSpace
          (Point (X.obj.obj ⨯ yoneda.obj (Over.mk (T.fromSpecResidueField t)))) ↔
        PreconnectedSpace {x : Point X.obj.obj | ∃ p : PointRepresentative X.obj.obj,
          Quot.mk _ p = x ∧ p.base (IsLocalRing.closedPoint p.K) = t}) ∧
      (Nonempty (Point (X.obj.obj ⨯ yoneda.obj (Over.mk (T.fromSpecResidueField t)))) ↔
        Nonempty {x : Point X.obj.obj | ∃ p : PointRepresentative X.obj.obj,
          Quot.mk _ p = x ∧ p.base (IsLocalRing.closedPoint p.K) = t}) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
