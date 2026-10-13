/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of affine morphisms along fpqc coverings

Source: Stacks Project, Descent, Lemma Tag 02L5, descent direction
(blueprint: lem-weil-pbc-fpqc-descend-affine).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-fpqc-descend-affine) Stacks Project, Descent, Tag 02L5:
a morphism is affine if its base changes along an fpqc covering family are affine.

Proof outline, following the eight steps of the node:
1. Affineness is invariant under isomorphism and local on the target for the Zariski topology
   [pqf-lem-affine-local-target], giving conditions (0) and (2) of
   [lem-weil-pbc-fpqc-local-on-base-criterion].
2. Affineness is stable under base change [lem-weil-pbc-affine-morphism-permanence],
   giving condition (1).
3. For condition (3), take a flat surjection of affine bases `S' → S` with affine base change.
   The covering map is affine and quasi-compact, and the base-changed source `X'` is affine
   [lem-weil-pbc-morphism-affine-schemes-affine, lem-weil-pbc-affine-morphism-permanence].
4. Quasi-compactness and separatedness descend
   [lem-weil-pbc-fpqc-descend-quasi-compact, lem-weil-pbc-fpqc-descend-separated], so `X` is
   quasi-compact and quasi-separated [lem-weil-pbc-qcqs-over-affine].
5. Flat base change identifies `Γ(X')` with `Γ(X) ⊗ Γ(S')`
   [lem-weil-pbc-flat-base-change-global-sections-qcqs].
6. The canonical map `X → Spec Γ(X)` [lem-weil-pbc-morphism-into-affine-scheme] base changes
   to an isomorphism: use the tensor description of the affine fibre product
   [lem-weil-pbc-fibre-product-affine-spectra] and cartesian square pasting
   [lem-weil-pbc-cartesian-square-pasting] to identify its base change with the affine
   source's canonical map.
7. The base-changed covering is flat and surjective
   [lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-surjective-base-change], and
   quasi-compact as a map of affine schemes. Isomorphisms descend
   [lem-weil-pbc-fpqc-descend-isomorphism], so `X` is affine, and its map to the affine base
   is affine [lem-weil-pbc-morphism-affine-schemes-affine]. This proves condition (3).
8. Apply [lem-weil-pbc-fpqc-local-on-base-criterion] to the given covering family.
-/
theorem isAffineHom_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, IsAffineHom (pullback.snd f (g i))) : IsAffineHom f := by
  have := IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @IsAffineHom)
    (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
