/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.GroupoidScheme
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# Separated algebraic spaces of dimension at most one are schemes

Source: Stacks Project, Spaces over Fields, Tag 0ADD,
`lemma-codim-1-point-in-schematic-locus`, applied at every point; Schemes, Tag 01JJ
(blueprint: lem-sfb-separated-space-dimension-one-scheme).

All presheaves are on schemes over `Spec K`. Thus their categorical product is the
product over `Spec K`, and the displayed diagonal is the relative diagonal. The point
space and its atlas topology are the existing `Point` and `pointTopologicalSpace`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated algebraic space locally of finite type over a field, of topological
Krull dimension at most one, is represented by a scheme over that field. No
quasi-compactness, properness, reducedness, connectedness or nonemptiness is assumed.

Source: Stacks Project, Spaces over Fields, Tag 0ADD,
`lemma-codim-1-point-in-schematic-locus`; Schemes, Tag 01JJ
(blueprint: lem-sfb-separated-space-dimension-one-scheme).

Proof:
1. Every etale scheme chart is locally Noetherian by pqf-lem-locnoeth-lft, since a
   field is Noetherian. By lem-a1-space-affine-atlas-open-cover and
   lem-a1-space-etale-open-image, cover the space by quasi-compact open subspaces
   with affine etale atlases. Separatedness restricts to these opens, which are
   therefore Noetherian (pqf-def-locnoeth).
2. Each open subspace has dimension at most one: closure takes a strict chain of
   irreducible closed subsets of the open to one in the whole space, and intersection
   with the open recovers the chain. Apply lem-sfb-noetherian-space-finite-scheme-cover
   to get a finite surjective scheme cover. Its source has dimension at most one by
   lem-sfb-finite-space-morphism-topology and
   lem-sfb-space-quasifinite-source-dimension-bound. Hence its local rings have
   dimension at most one by lem-pc-scheme-dimension-local-rings.
3. The scheme fibre product of this finite cover with itself gives a finite groupoid
   (def-trf-algebraic-space, def-a1-groupoid-scheme). By
   lem-a1-space-fibre-product-point its orbit over a point is exactly the finite fibre.
   Apply lem-sfb-finite-groupoid-codimension-one-invariant-affine to find an invariant
   affine open containing that fibre.
4. This open is saturated by the fibre-product point criterion. The finite surjection
   is closed by lem-sfb-finite-space-morphism-topology, so its image is open. By
   lem-a1-space-etale-open-image this is an open subspace, and the affine source is
   precisely its pullback. The restricted finite surjection has a Noetherian separated
   target; lem-sfb-noetherian-space-finite-affine-descent makes that target affine.
5. These representable open neighbourhoods cover all points. Their scheme pullbacks
   cover every scheme test by lem-a1-space-etale-open-image. The fppf sheaf is a
   Zariski sheaf, so lem-pc-schemes-criterion glues them to a representing scheme over
   the field. For the empty space the empty cover gives the empty scheme.
-/
theorem exists_scheme_of_separated_dim_le_one {K : Type u} [Field K]
    (X : AlgebraicSpace (Spec (.of K)))
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj)))
    (hlft : ∀ (U : Over (Spec (.of K))) (a : yoneda.obj U ⟶ X.obj.obj),
      IsEtale a → LocallyOfFiniteType U.hom)
    (hdim : topologicalKrullDim (Point X.obj.obj) ≤ 1) :
    ∃ U : Over (Spec (.of K)), Nonempty (yoneda.obj U ≅ X.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
