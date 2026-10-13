/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Over

/-! # The geometric part of the affine-cover acyclic embedding

Source: Stacks Project, Tag 0BDY, construction in part (1).
(blueprint: lem-sc-picard-affine-cover-module-embedding).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A quasi-coherent module embeds in a pushforward from an affine cover source.
Source: Stacks Project, Cohomology of Schemes, Tag 0BDY, proof of part (1).
(blueprint: lem-sc-picard-affine-cover-module-embedding).

Proof: Choose a finite affine open cover of X by quasi-compactness, and form the finite
coproduct U of its members. A finite disjoint union of affine schemes is affine (its
coordinate ring is the finite product of the coordinate rings). Let j : U → X be the
cover morphism. For any affine open V in X, each intersection of V with a cover member
is affine by the affine-diagonal intersection lemma. Therefore j⁻¹(V), their finite
disjoint union, is affine, and j is an affine morphism. Set G = j*F, the actual module
pullback along j, which preserves quasi-coherence. Take i to be the pullback/pushforward
adjunction unit. At x choose a cover member containing x; restriction to the corresponding
point of U identifies the pullback stalk with F_x and provides a left inverse to i_x.
Thus every stalk map is injective, so i is a monomorphism. For empty X use the empty
finite cover; its coproduct is the spectrum of the zero ring, and the stalk condition
is vacuous. The field hypothesis does not enter the construction. No cohomology or
acyclicity assertion is included in this geometric lemma. -/
theorem exists_affine_cover_module_embedding (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k)))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent] :
    ∃ (U : Scheme.{u}) (j : U ⟶ X)
      (G : SheafOfModules.{u} (moduleRings U.toRingedSpace)),
      IsAffine U ∧ IsAffineHom j ∧ G.IsQuasicoherent ∧
        ∃ i : F ⟶ (Modules.pushforward j).obj G, Mono i := by
  sorry

end AlgebraicGeometry.Scheme
