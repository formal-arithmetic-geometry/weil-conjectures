/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Stalks of pushforward along a closed immersion

Source: Stacks Project, Sheaves, Lemma 00AE and Modules, Lemma 08KS
(blueprint: lem-weil-pbc-closed-pushforward-stalks).
-/

universe w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

noncomputable section

/-- Stalks of the pushforward of a module along a morphism of schemes whose underlying map
is a closed embedding: (1) the stalk of `i_* G` vanishes off the closed image; (2) the germ map
`c_z = stalkPushforward : (i_* G)_{i(z)} → G_z` is bijective (an isomorphism) and linear over
`O_{X,i(z)}` acting on `G_z` through `i^♯_z = i.stalkMap z`; (3) `c_z` is natural in `G`.
Source: Stacks Project, Sheaves, Lemma 00AE and Modules, Lemma 08KS
(blueprint: lem-weil-pbc-closed-pushforward-stalks).
Proof: for `x ∉ i(Z)` the open `X \ i(Z)` is a neighbourhood of `x` with empty preimage, so
every germ is zero. For `z ∈ Z` the opens `i⁻¹V`, `V ∋ i(z)`, are cofinal among the
neighbourhoods of `z` (an open `U ∋ z` is `i⁻¹V` for `V = W ∪ (X \ i(Z))` with `W ∩ i(Z) = i(U)`),
so `c_z` is bijective; linearity is the germ rule `(a s)_z = i^♯(a_{i(z)}) s_z` for
`a ∈ O_X(V)`, `s ∈ G(i⁻¹V)`; naturality holds on germs.
-/
theorem closedImmersion_pushforward_stalks
    {X Z : Scheme.{w}} (i : Z ⟶ X)
    (h : Topology.IsClosedEmbedding i.base) (G : Z.Modules) :
    (∀ x : X, x ∉ Set.range i.base →
      Subsingleton (↥(TopCat.Presheaf.stalk ((Scheme.Modules.pushforward i).obj G).presheaf x))) ∧
    (∀ z : Z,
      Function.Bijective
        (ConcreteCategory.hom
          (TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf z)) ∧
      IsIso (TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf z) ∧
      ∀ (r : X.presheaf.stalk (i.base z))
        (m : ↥(TopCat.Presheaf.stalk
          ((Scheme.Modules.pushforward i).obj G).val.presheaf (i.base z))),
        ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab i.base G.val.presheaf z)
            (r • m) =
          (i.stalkMap z).hom r •
            ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab i.base G.val.presheaf z)
              m) ∧
    (∀ H : Z.Modules, ∀ φ : G ⟶ H, ∀ z : Z,
      (TopCat.Presheaf.stalkFunctor Ab (i.base z)).map
          ((Scheme.Modules.pushforward i).map φ).mapPresheaf ≫
          (TopCat.Presheaf.stalkPushforward Ab i.base H.presheaf z) =
        (TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf z) ≫
          (TopCat.Presheaf.stalkFunctor Ab z).map φ.mapPresheaf) := by
  sorry

end
end AlgebraicGeometry
