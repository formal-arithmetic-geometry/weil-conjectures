/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.AffineFanHomUniversal

/-!
# Spreading a prescribed comparison of normalized affine fan opens

Source: ILO VIII, proof of 3.3.15, printed p.109, shrinking the common inverse image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.FineFan

/-- A supplied comparison of affine opens spreads from its normalized stalk equation.
The comparison is part of the input: this lemma constructs neither it nor the monoid
isomorphism. The monoid map need not even be invertible.

Source: ILO VIII, proof of 3.3.15, printed p.109, the common inverse image and shrinking
for fine monoids, followed by Lemma 3.1.8(ii), p.99
(blueprint: lem-trf-affine-open-germ-comparison).

Proof: Let V be the intersection of the inverse images of the two given opens; it
contains t. Restrict h and k to V and factor them through the respective opens, using
the ordinary restriction of their sheaf maps. Compose the second factorization with e.
Compose both with the target affine coordinates. Naturality of germs, the two supplied
normalizations and the section equation for e identify their canonical section germs
with stalkMap(h)(p) and stalkMap(k)(alpha(p)), pulled back along V -> T. These agree by
the supplied stalk equation. The stalks on V are sharp and both maps are local, since
open restriction preserves stalks and the coordinate isomorphisms are local. Apply
lem-trf-affine-fan-germ-rigidity to the fine sharp target stalk. It shrinks V around t
and equates both morphisms, including all sheaf maps. Regard the resulting open of V
as an open U of T. Restrict the two factorizations to U and cancel the target coordinate
isomorphism to obtain a = b followed by e. Their triangles are the restriction triangles.
The two containments follow from U contained in V. For the trivial monoid, the rigidity
lemma keeps V without choosing a generator; empty opens cannot contain t. -/
theorem affine_open_germ_comparison
    (T : SheafedSpace CommMonCat.{u})
    (hT : ∀ x : T, IsSharp (stalk T.presheaf x))
    (F G : Fan.{u}) (h : T ⟶ F.space) (k : T ⟶ G.space)
    (hh : IsLocalMorphism h) (hk : IsLocalMorphism k) (t : T)
    (L : AffineOpen F.space (stalk F.space.presheaf (h.hom.base t)))
    (K : AffineOpen G.space (stalk G.space.presheaf (k.hom.base t)))
    (hL : h.hom.base t ∈ L.openSet) (hK : k.hom.base t ∈ K.openSet)
    (hf : IsFine (stalk F.space.presheaf (h.hom.base t)))
    (nL : ∀ p : stalk F.space.presheaf (h.hom.base t),
      germ (F.space.restrict L.openSet.isOpenEmbedding).presheaf ⊤
          ⟨h.hom.base t, hL⟩ (by trivial) (affinePullback L.iso.hom p) =
        stalkMap (F.space.ofRestrict L.openSet.isOpenEmbedding) ⟨h.hom.base t, hL⟩ p)
    (nK : ∀ q : stalk G.space.presheaf (k.hom.base t),
      germ (G.space.restrict K.openSet.isOpenEmbedding).presheaf ⊤
          ⟨k.hom.base t, hK⟩ (by trivial) (affinePullback K.iso.hom q) =
        stalkMap (G.space.ofRestrict K.openSet.isOpenEmbedding) ⟨k.hom.base t, hK⟩ q)
    (α : stalk F.space.presheaf (h.hom.base t) →*
      stalk G.space.presheaf (k.hom.base t))
    (ha : (stalkMap k t).hom.comp α = (stalkMap h t).hom)
    (e : G.space.restrict K.openSet.isOpenEmbedding ≅
      F.space.restrict L.openSet.isOpenEmbedding)
    (he : (SheafedSpace.Γ.map e.hom.op).hom.comp (affinePullback L.iso.hom) =
      (affinePullback K.iso.hom).comp α) :
    ∃ U : Opens T, t ∈ U ∧
      (∀ x ∈ U, h.hom.base x ∈ L.openSet) ∧
      (∀ x ∈ U, k.hom.base x ∈ K.openSet) ∧
      ∃ (a : T.restrict U.isOpenEmbedding ⟶ F.space.restrict L.openSet.isOpenEmbedding)
        (b : T.restrict U.isOpenEmbedding ⟶ G.space.restrict K.openSet.isOpenEmbedding),
        a ≫ F.space.ofRestrict L.openSet.isOpenEmbedding =
          T.ofRestrict U.isOpenEmbedding ≫ h ∧
        b ≫ G.space.ofRestrict K.openSet.isOpenEmbedding =
          T.ofRestrict U.isOpenEmbedding ≫ k ∧
        a = b ≫ e.hom := by sorry

end AlgebraicGeometry.FineFan
