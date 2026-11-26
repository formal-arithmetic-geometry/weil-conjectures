/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Functors
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Stalks of closed-subset pushforward for abelian sheaves

## References

* Stacks Project, Tag 00AE.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace Topology
open TopCat

namespace TopCat

/-- Stalks of the direct image of an abelian sheaf along a closed embedding: the stalk at a
point of the image is the original stalk, naturally in the sheaf, and the stalk at a point off
the image is zero. -/
theorem closedPushforwardAbelianStalks
    {X : TopCat.{u}} (C : Set X) (hC : IsClosed C)
    (F : (TopCat.of C).Sheaf AddCommGrpCat.{u}) :
    (∀ x : X, x ∉ C →
      IsZero (TopCat.Presheaf.stalk
        ((TopCat.Sheaf.pushforward AddCommGrpCat
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).obj F).1 x)) ∧
    (∀ z : (TopCat.of C),
      IsIso (TopCat.Presheaf.stalkPushforward AddCommGrpCat
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) F.1 z)) ∧
    (∀ (G : (TopCat.of C).Sheaf AddCommGrpCat.{u}) (φ : F ⟶ G)
      (z : (TopCat.of C)),
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat
        (Subtype.val z)).map
          ((TopCat.Presheaf.pushforward AddCommGrpCat
            (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)).map φ.1) ≫
          TopCat.Presheaf.stalkPushforward AddCommGrpCat
            (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) G.1 z =
        TopCat.Presheaf.stalkPushforward AddCommGrpCat
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) F.1 z ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat z).map φ.1) := by
  let i : TopCat.of C ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let P := (TopCat.Presheaf.pushforward AddCommGrpCat i).obj F.1
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change IsZero (P.stalk x)
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    suffices h : ∀ t : P.stalk x, t = 0 from
      ⟨fun a b ↦ (h a).trans (h b).symm⟩
    intro t
    obtain ⟨V, hV, hxV, s, rfl⟩ :=
      P.exists_le_germ_eq t (V := ⟨Cᶜ, hC.isOpen_compl⟩) hx
    have he : (Opens.map i).obj V = ⊥ := by
      ext z
      exact ⟨fun hz ↦ (hV hz) z.property, fun hz ↦ False.elim hz⟩
    have hz := (F.isTerminalOfEqEmpty he).isZero
    have hs : s = 0 := (AddCommGrpCat.isZero_iff_subsingleton.mp hz).elim _ _
    rw [hs]
    exact map_zero _
  · intro z
    exact Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat Topology.IsInducing.subtypeVal F.1 z
  · intro G φ z
    apply Presheaf.stalk_hom_ext P
    intro V hxV
    change P.germ V (i z) hxV ≫
      (Presheaf.stalkFunctor AddCommGrpCat (i z)).map
        ((Presheaf.pushforward AddCommGrpCat i).map φ.1) ≫
        Presheaf.stalkPushforward AddCommGrpCat i G.1 z =
      P.germ V (i z) hxV ≫ Presheaf.stalkPushforward AddCommGrpCat i F.1 z ≫
        (Presheaf.stalkFunctor AddCommGrpCat z).map φ.1
    rw [Presheaf.stalkFunctor_map_germ_assoc]
    conv_rhs => rw [← Category.assoc]
    erw [Presheaf.stalkPushforward_germ]
    dsimp only [P]
    erw [Presheaf.stalkPushforward_germ, Presheaf.stalkFunctor_map_germ]
    rfl

end TopCat
