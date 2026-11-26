/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Transport of sheaves and direct images along the image of an embedding

## References

* Stacks Project, Tag 09ZG.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

private theorem homeomorph_opens_dense
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    e.opensCongr.equivalence.functor.IsDenseSubsite
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) := by
  let E := e.opensCongr.equivalence
  change E.functor.IsDenseSubsite _ _
  refine { functorPushforward_mem_iff := ?_ }
  intro U R
  constructor
  · intro h x hx
    have hx' : e x ∈ E.functor.obj U := by
      change e.symm (e x) ∈ U
      simpa using hx
    obtain ⟨V, f, ⟨W, g, k, hg, _⟩, hv⟩ := h (e x) hx'
    refine ⟨W, g, hg, ?_⟩
    have hw := k.le hv
    change e.symm (e x) ∈ W at hw
    simpa using hw
  · intro h y hy
    change e.symm y ∈ U at hy
    obtain ⟨V, f, hf, hv⟩ := h (e.symm y) hy
    refine ⟨E.functor.obj V, E.functor.map f, ?_, hv⟩
    exact ⟨V, f, 𝟙 _, hf, (Category.id_comp _).symm⟩

/-- The homeomorphisms of the ambient spaces and the embedded subspaces give
compatible equivalences of sheaf categories and of global sections. Only direct
images occur here; no inverse-image adjunction or restriction unit is used. -/
theorem embedding_pushforward_transport
    {X Z : TopCat.{u}} (i : Z ⟶ X) (hi : Topology.IsEmbedding i)
    (Y : TopCat.{u + 1}) (e : Y ≃ₜ X) :
    let D : Set Y := e ⁻¹' Set.range i
    let j : TopCat.of D ⟶ Y := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    ∃ (T : X.Sheaf (Type (u + 1)) ≌ Y.Sheaf (Type (u + 1)))
      (S : Z.Sheaf (Type (u + 1)) ≌ (TopCat.of D).Sheaf (Type (u + 1))),
      Nonempty
        (sheafToPresheaf (Opens.grothendieckTopology X) (Type (u + 1)) ⋙
            (evaluation (Opens X)ᵒᵖ (Type (u + 1))).obj (op ⊤) ≅
          T.functor ⋙ sheafToPresheaf (Opens.grothendieckTopology Y) (Type (u + 1)) ⋙
            (evaluation (Opens Y)ᵒᵖ (Type (u + 1))).obj (op ⊤)) ∧
      Nonempty
        ((Opens.map i).sheafPushforwardContinuous (Type (u + 1))
            (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z) ⋙ T.functor ≅
          S.functor ⋙ Sheaf.pushforward (Type (u + 1)) j) := by
  classical
  dsimp only
  let D : Set Y := e ⁻¹' Set.range i
  let j : TopCat.of D ⟶ Y := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let h : D ≃ₜ Z :=
    (e.subtype (fun _ ↦ Iff.rfl)).trans hi.toHomeomorph.symm
  let E := e.symm.opensCongr.equivalence
  let H := h.symm.opensCongr.equivalence
  have : E.inverse.IsDenseSubsite
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    homeomorph_opens_dense e
  have : H.inverse.IsDenseSubsite
      (Opens.grothendieckTopology D) (Opens.grothendieckTopology Z) :=
    homeomorph_opens_dense h
  let T := E.sheafCongr (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) (Type (u + 1))
  let S := H.sheafCongr (Opens.grothendieckTopology Z)
    (Opens.grothendieckTopology D) (Type (u + 1))
  refine ⟨T, S, ⟨?_⟩, ⟨?_⟩⟩
  · refine NatIso.ofComponents (fun F ↦ F.obj.mapIso (eqToIso ?_)) ?_
    · change op ⊤ = op (E.inverse.obj ⊤)
      congr 1
    · intro F G f
      exact (f.hom.naturality _).symm
  · refine NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ (Iso.refl _)) ?_
    intro F G f
    rfl

end TopCat
