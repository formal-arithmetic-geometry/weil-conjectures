/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Topology.Maps.Basic

/-!
# Open immersions respect open immersions on the right

The `MorphismProperty.RespectsRight` instance for open immersions of schemes.

We also record two auxiliary statements: a morphism whose composite with an open
immersion is an isomorphism onto the range of that open immersion is itself an
isomorphism (`AlgebraicGeometry.exists_isIso_lift_of_mem_iff`), and closedness of a
subset of a scheme can be checked on the members of an open cover
(`AlgebraicGeometry.Scheme.isClosed_of_openCover`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance : MorphismProperty.RespectsRight @IsOpenImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf ↦ by
    have : IsOpenImmersion i := hi
    have : IsOpenImmersion f := hf
    infer_instance⟩

/-- An open immersion whose range is an open `B` is an isomorphism onto `B`. -/
lemma exists_isIso_lift_of_mem_iff {Y Z : Scheme.{u}} (m : Z ⟶ Y)
    (hm : IsOpenImmersion m) {B : Y.Opens} (hB : ∀ y, (∃ z, m z = y) ↔ y ∈ B) :
    ∃ m' : Z ⟶ B.toScheme, IsIso m' ∧ m' ≫ B.ι = m := by
  have := hm
  have hsub : Set.range m.base ⊆ Set.range B.ι.base := by
    rintro - ⟨z, rfl⟩
    exact ⟨⟨m z, (hB _).mp ⟨z, rfl⟩⟩, rfl⟩
  refine ⟨IsOpenImmersion.lift B.ι m hsub, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  have hfac : IsOpenImmersion.lift B.ι m hsub ≫ B.ι = m := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (IsOpenImmersion.lift B.ι m hsub) := by
    have h1 : IsOpenImmersion (IsOpenImmersion.lift B.ι m hsub ≫ B.ι) := by
      rw [hfac]; infer_instance
    exact IsOpenImmersion.of_comp _ B.ι
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun t ↦ ?_)
  obtain ⟨z, hz⟩ := (hB t.1).mpr t.2
  refine ⟨z, B.ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, hfac]
  exact hz

/-- A set in a scheme is closed as soon as its preimage under each member of a jointly
surjective family of open immersions is closed. -/
lemma Scheme.isClosed_of_openCover {Q : Scheme.{u}} {κ : Type*} {Z : κ → Scheme.{u}}
    (q : ∀ k, Z k ⟶ Q) [∀ k, IsOpenImmersion (q k)] (hcov : ∀ x : Q, ∃ k y, q k y = x)
    {s : Set Q} (hs : ∀ k, IsClosed ((q k).base ⁻¹' s)) : IsClosed s :=
  isClosed_of_isOpenEmbedding_cover (fun k ↦ (q k).base)
    (fun k ↦ (q k).isOpenEmbedding) hcov hs

end AlgebraicGeometry
