/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Connected components after extension of a separably closed field

Source: Stacks Project, Varieties, Tag 0363, first assertion
(blueprint: lem-weil-pbc-sepclosed-field-components-bijection).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Over a separably closed field, arbitrary field extension induces a bijection on connected
components of any scheme. The map sends the component of a point to the component of its image
under the first projection. No finiteness or nonemptiness assumption is needed.

Source: Stacks Project, Varieties, Tag 0363, first assertion
(blueprint: lem-weil-pbc-sepclosed-field-components-bijection).

Proof plan:
1. Put `W = Spec L`. Its underlying space has exactly one point because `L` is a field, hence
   it is nonempty and connected (def-weil-affine-spectrum, def-weil-connected-scheme).
2. Apply `GeometricallyConnected.of_connectedSpace_of_isSepClosed` to `W → Spec k`:
   `k` is separably closed and `W` is connected, so `W` is geometrically connected
   (lem-weil-separably-closed-geometrically-connected).
3. Apply Tag 0385 (lem-weil-pbc-geometrically-connected-product-components), represented by
   `Scheme.Hom.connectedComponentsHomeomorph`, to `W ×[Spec k] Z → Z`. The projection is
   geometrically connected by base change and open since schemes over a field are universally
   open. Swap the factors using the fibre-product universal property (def-pc-fibre-product).
   The swap and its inverse preserve maximal nonempty connected subsets, and commute with the
   projections to `Z`. Thus the resulting bijection is the component map of the first projection
   `Z ×[Spec k] W → Z`. If `Z` is empty, both component types are empty; the same argument imposes
   no finiteness condition on either component type or on `L/k`. -/
theorem bijective_connectedComponentsMap_pullback_fst_of_isSepClosed
    (k L : Type u) [Field k] [IsSepClosed k] [Field L] [Algebra k L]
    (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of k))] :
    Function.Bijective
      (pullback.fst (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).continuous.connectedComponentsMap := by
  have : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    GeometricallyConnected.of_connectedSpace_of_isSepClosed _
  let p := pullback.fst (Z ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L)))
  let e := p.connectedComponentsHomeomorph p.isOpenMap
  have he : e = p.continuous.connectedComponentsMap := by
    funext c
    exact Scheme.Hom.connectedComponentsHomeomorph_apply p p.isOpenMap c
  rw [← he]
  exact e.bijective

end AlgebraicGeometry
