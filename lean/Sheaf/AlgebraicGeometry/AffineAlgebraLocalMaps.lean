/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf

/-! # Local maps determined by a morphism of structure algebras

Source: Stacks Project, Morphisms, Lemma 01SA; Constructions, Lemma 01LT.
(blueprint: lem-weil-pbc-affine-algebra-local-maps).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option hygiene false in
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

/-- An algebra morphism gives compatible scheme maps on inverse images of affine opens.
Source: Stacks Project, Morphisms, Lemma 01SA; Constructions, Lemma 01LT;
parts (i) and (iii) of the local proof of the affine structure-algebra correspondence.
(blueprint: lem-weil-pbc-affine-algebra-local-maps).

Proof: For each affine open U of S, the inverse image of U under g is affine.
The Gamma--Spec adjunction applied to the component of α on U, conjugated by the
canonical top-section isomorphisms of both open subschemes, gives a map from the
inverse image under f to the inverse image under g. The commutativity condition
of the algebra morphism says that its composite to U agrees with the restricted
map f: this follows by injectivity of the Gamma--Spec correspondence for the affine U.
Compose with the open immersion into Y to obtain k_U. Its section map is the prescribed
component by construction, including the stated top-section transport.

For an affine V contained in U, compare k_V with the restriction of k_U. Both factor
through the affine inverse image of U under g. Naturality of α gives equality of
their global section maps, and injectivity of the adjunction gives equality of maps.
For arbitrary affine U and V, their intersection need not be affine. Cover it by
affine W contained in both. On the inverse image of each W both maps agree with k_W,
by the preceding comparison. Scheme-morphism uniqueness on this open cover gives
the displayed equality on the pullback of the two open immersions. No affineness
of X is required, and the empty inverse images and empty base are covered by the
same adjunction and the uniqueness assertion for the empty cover. -/
theorem affine_algebra_local_maps {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom g] (α : (𝒪⁎g : S.CommAlgebraSheaf) ⟶ 𝒪⁎f) :
    ∃ k : ∀ U : S.affineOpens, (f ⁻¹ᵁ U.1).toScheme ⟶ Y,
      (∀ U, k U ≫ g = (f ⁻¹ᵁ U.1).ι ≫ f) ∧
      (∀ U V, Limits.pullback.fst (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫ k U =
        Limits.pullback.snd (f ⁻¹ᵁ U.1).ι (f ⁻¹ᵁ V.1).ι ≫ k V) ∧
      (∀ (U : S.affineOpens) (e : ⊤ ≤ k U ⁻¹ᵁ (g ⁻¹ᵁ U.1)),
        (k U).appLE (g ⁻¹ᵁ U.1) ⊤ e =
          α.right.hom.app (op U.1) ≫ (f ⁻¹ᵁ U.1).topIso.inv) := by sorry

end AlgebraicGeometry
