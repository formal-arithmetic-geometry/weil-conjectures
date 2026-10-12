/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Comparison of restriction units under a change of topological universe

Source: Stacks Project, Tag 09ZG, closed-image and universe-transport step.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat

/-- Restriction along an embedding is conjugate to restriction to its image after
transport by a homeomorphism, even when the ambient spaces have different universes.
No spectrality, closedness, or connectedness is required for this comparison.

Source: Stacks Project, Tag 09ZG, closed-image and universe-transport step;
Mathlib `Adjunction.unit_leftAdjointUniq_hom_app` supplies the unit comparison.
(blueprint: lem-weil-pbc-closed-embedding-restriction-transport-square)

Proof:
1. The homeomorphism `e` gives an order isomorphism of open sets. Precompose `G`
   with its functor on opposite open sets to obtain `F`. A homeomorphism preserves
   open covers and their pullbacks, so matching families and their unique gluings
   correspond, and `F` is a sheaf. At the top open this gives the equivalence `a`.
2. Since `i` is an embedding, its range with the subspace topology is homeomorphic
   to its domain. Combining this homeomorphism with the restriction of `e` gives
   a homeomorphism between `Z` and `D`. Precomposition on opens identifies the two
   pushforward functors under these sheaf equivalences.
3. Transport the inverse-image adjunction along these equivalences. Its right
   adjoint is the identified pushforward. Uniqueness of left adjoints yields an
   isomorphism from the transported inverse image to the inverse image along `j`.
   The equation `Adjunction.unit_leftAdjointUniq_hom_app` says that this comparison
   preserves the units. Evaluating the comparison and the domain homeomorphism
   at the top open gives `b`, and evaluating the unit equation gives the displayed
   commuting square. All comparison maps are equivalences. This includes empty
   spaces and empty images; no choice of a point is used. -/
theorem closed_embedding_restriction_transport_square
    {X Z : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsEmbedding i)
    (Y : TopCat.{u + 1}) (e : Y ≃ₜ X) :
    letI : ∀ P : (Opens X)ᵒᵖ ⥤ Type (u + 1),
        (Opens.map i).op.HasPointwiseLeftKanExtension P :=
      fun P U ↦ @Types.hasColimit.{u, u + 1, u}
        (CostructuredArrow.{u, u, u, u} (Opens.map i).op U)
        inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
    let A := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map i) (Type (u + 1))
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)
    let D : Set Y := e ⁻¹' Set.range i
    let j : TopCat.of D ⟶ Y := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let B := Sheaf.pullbackPushforwardAdjunction (Type (u + 1)) j
    ∀ G : X.Sheaf (Type (u + 1)),
      ∃ (F : Y.Sheaf (Type (u + 1)))
        (a : G.1.obj (op ⊤) ≃ F.1.obj (op ⊤))
        (b : ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map i)
          (Type (u + 1)) (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Z)).obj G).1.obj (op ((Opens.map i).obj ⊤)) ≃
          ((Sheaf.pullback (Type (u + 1)) j).obj F).1.obj (op ((Opens.map j).obj ⊤))),
        ∀ s, b ((A.unit.app G).hom.app (op ⊤) s) =
          (B.unit.app F).hom.app (op ⊤) (a s) := by sorry

end TopCat
