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
# Complements on open immersions of schemes

- the `MorphismProperty.RespectsRight` instance for open immersions;
- `AlgebraicGeometry.exists_isIso_lift_of_opensRange_eq`: an open immersion whose range is
  an open `B` of the target is an isomorphism onto `B`;
- `AlgebraicGeometry.Scheme.isClosed_of_openCover`: closedness of a subset of a scheme can
  be checked on the members of an open cover.
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

/-- An open immersion whose range is the open `B` is an isomorphism onto `B`. -/
lemma exists_isIso_lift_of_opensRange_eq {Y Z : Scheme.{u}} (m : Z ⟶ Y)
    [IsOpenImmersion m] {B : Y.Opens} (hB : m.opensRange = B) :
    ∃ m' : Z ⟶ B.toScheme, IsIso m' ∧ m' ≫ B.ι = m := by
  have hmem : ∀ y, (∃ z, m z = y) ↔ y ∈ B := fun y ↦ by rw [← hB]; exact Iff.rfl
  have hsub : Set.range m.base ⊆ Set.range B.ι.base := by
    rintro - ⟨z, rfl⟩
    exact ⟨⟨m z, (hmem _).mp ⟨z, rfl⟩⟩, rfl⟩
  refine ⟨IsOpenImmersion.lift B.ι m hsub, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  have hfac : IsOpenImmersion.lift B.ι m hsub ≫ B.ι = m := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (IsOpenImmersion.lift B.ι m hsub) := by
    have h1 : IsOpenImmersion (IsOpenImmersion.lift B.ι m hsub ≫ B.ι) := by
      rw [hfac]; infer_instance
    exact IsOpenImmersion.of_comp _ B.ι
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun t ↦ ?_)
  obtain ⟨z, hz⟩ := (hmem t.1).mpr t.2
  refine ⟨z, B.ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, hfac]
  exact hz

/-- A set in a scheme is closed as soon as its preimage under each member of a jointly
surjective family of open immersions is closed. -/
lemma Scheme.isClosed_of_openCover {Q : Scheme.{u}} {κ : Type*} {Z : κ → Scheme.{u}}
    (q : ∀ k, Z k ⟶ Q) [∀ k, IsOpenImmersion (q k)] (hcov : ∀ x : Q, ∃ k y, q k y = x)
    {s : Set Q} (hs : ∀ k, IsClosed ((q k).base ⁻¹' s)) : IsClosed s :=
  Topology.isClosed_of_isOpenEmbedding_cover (fun k ↦ (q k).base)
    (fun k ↦ (q k).isOpenEmbedding) hcov hs

end AlgebraicGeometry
