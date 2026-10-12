/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec
import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraColimit

/-! # Including a limit of affine schemes in all schemes over the base

Source: Stacks Project, Limits, Lemmas 01YX and 01YW, the local universal-property
argument in the relative-spectrum construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A directed inverse limit in schemes affine over `S` is also a limit in `Over S`.

Source: Stacks Project, Limits, Lemma 01YX (lemma-directed-inverse-system-has-limit),
the universal-property argument, using Lemma 01YW on each affine open of the base.
(blueprint: lem-weil-pbc-affine-over-limit-inclusion)

Proof: use the anti-equivalence between affine S-schemes and quasi-coherent S-algebras.
The given limiting cone corresponds to a colimit cocone. Construct the colimit in all
algebra sheaves by quasiCoherentAlgebra_colimit; it is quasi-coherent, hence also a colimit
in the full quasi-coherent subcategory. Uniqueness identifies it with the given colimit.
Its sections on every affine open U of S are the colimit of the stage section rings.
Relative-spectrum charts therefore identify the restrictions of the given cone over U
with the limiting spectrum cone of these rings (01YW).
For any cone in Over S with vertex T, use its given S-map. Over each affine U of S,
the restricted cone has a unique factorization into the restricted vertex,
by the affine spectrum limit.
Choose any index j. Composing this factorization with the j-th projection and then
the structure map to U gives the given map from the test scheme to U. Thus the
factorization is over U. In particular it restricts to inverse images of every
smaller affine base open W; this uses nonemptiness of J.
On overlaps, cover U intersect V by affine opens W of S. The two factorizations restrict
to the unique factorization over each W, so agree on the overlap. Glue these morphisms
on the open cover of T by the inverse images of affine opens of S. Their projection
identities hold on this cover and hence globally. The glued morphism is over S since this
holds on every open of the cover. Any second factorization over S restricts to the same
unique factorization on every U;
therefore it equals the glued morphism. This proves the universal property in Over S.
No quasi-separatedness of S or T is needed: intersections are covered by affine opens,
rather than assumed affine. -/
theorem isLimit_affineOver_inclusion
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (S : Scheme.{u})
    (F : Jᵒᵖ ⥤ ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))
    (c : Cone F) (hc : IsLimit c) :
    Nonempty (IsLimit
      ((ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapCone c)) := by sorry

end AlgebraicGeometry
