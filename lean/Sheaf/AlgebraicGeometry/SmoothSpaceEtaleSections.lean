/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing

/-! # Étale local sections of a smooth surjective algebraic space

Source: Stacks Project, Spaces Topologies, Tag 0CFV (lemma-etale-dominates-smooth),
with More on Morphisms, Tags 055V and 0EY4
(blueprint: lem-sfb-smooth-space-cover-etale-sections).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A smooth surjective map from an algebraic space to a scheme has sections over a
jointly surjective étale scheme covering. Surjectivity is surjectivity on field-valued
point classes: its point image is the whole target point set. All schemes, test fields,
and the covering index set use the fixed small universe. The empty target admits the
empty covering; no nonemptiness, separation, finiteness, or characteristic restriction
is imposed.
Source: Stacks Project, Tag 0CFV, applied to the singleton smooth covering; its scheme
refinement is Tag 055V, alternatively obtained using Tag 0EY4
(blueprint: lem-sfb-smooth-space-cover-etale-sections).

Proof: (1) If T is empty, use an empty family; coverage and all lifting conditions
are vacuous.
(2) By lem-a1-space-affine-etale-cover choose a scheme atlas a : h_W → V, representable,
surjective and étale, and surjective on field-valued point classes. The composite
q = a ≫ p is a scheme map by Yoneda. The chartwise smoothness hypothesis makes q smooth.
Surjectivity on point classes of p and a makes q surjective on scheme points, using
the identification of scheme points with residue-field point classes.
(3) Apply sbc-lem-slicing, namely Smooth.exists_etaleCover_factorization, to q. It gives
an étale covering bᵢ : Uᵢ → W and factorizations bᵢ ≫ q = rᵢ ≫ eᵢ, with eᵢ : Tᵢ → T
étale and sections sᵢ : Tᵢ → Uᵢ of rᵢ. Give every scheme its induced map to S.
(4) Set vᵢ = sᵢ ≫ bᵢ ≫ a. Then vᵢ ≫ p = eᵢ since sᵢ ≫ rᵢ is the identity.
For t in T choose w over t using surjectivity of q, then u in some Uᵢ over w using the
covering bᵢ. Its image rᵢ(u) maps to t under eᵢ. Thus the eᵢ cover T. The index and all
schemes remain in the bounds of def-weil-size-convention, as do the atlas and slicing. -/
theorem exists_etale_local_sections {S : Scheme.{u}} (V : AlgebraicSpace S)
    (T : Over S) (p : V.obj.obj ⟶ yoneda.obj T)
    (hp : SpaceMapIsSmooth V T p) (hsurj : pointImage p = Set.univ) :
    ∃ (I : Type u) (Tᵢ : I → Over S) (e : ∀ i : I, Tᵢ i ⟶ T)
      (v : ∀ i : I, yoneda.obj (Tᵢ i) ⟶ V.obj.obj),
      (∀ i : I, Etale (e i).left) ∧
      (∀ t : T.left, ∃ (i : I) (tᵢ : (Tᵢ i).left), (e i).left.base tᵢ = t) ∧
      (∀ i : I, v i ≫ p = yoneda.map (e i)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
