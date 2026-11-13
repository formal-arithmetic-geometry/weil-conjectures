/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import WeilConjectures.AlgebraicGeometry.SectionComponentLocallyConstructible
import WeilConjectures.AlgebraicGeometry.SmoothSectionComponentGeneralization

/-!
# Openness of the fibre components meeting a smooth section

## References

* [Stacks Project, Tag 055R](https://stacks.math.columbia.edu/tag/055R)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a smooth, quasi-compact, quasi-separated morphism with a section, the union of
fibre connected components meeting the section is open. -/
theorem Smooth.isOpen_section_component {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    IsOpen {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  let S : Set P := {p | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))}
  have hcons : Topology.IsLocallyConstructible S :=
    isLocallyConstructible_section_component g σ hσ
  have hgen : StableUnderGeneralization S :=
    Smooth.stableUnderGeneralization_section_component g σ hσ
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨q, hq⟩ := P.affineCover.covers p
  let j := P.affineCover.f (P.affineCover.idx p)
  have hpre : IsOpen (j ⁻¹' S) := by
    exact PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
      (hgen.preimage j.continuous)
      ((hcons.preimage_of_isOpenEmbedding j.isOpenEmbedding).isConstructible)
  have hopen : IsOpen (j '' (j ⁻¹' S)) := j.isOpenEmbedding.isOpenMap _ hpre
  have hmem : p ∈ j '' (j ⁻¹' S) := by
    refine ⟨q, ?_, hq⟩
    change j q ∈ S
    rw [show j q = p from hq]
    exact hp
  exact Filter.mem_of_superset (hopen.mem_nhds hmem) (Set.image_preimage_subset j S)

end AlgebraicGeometry
