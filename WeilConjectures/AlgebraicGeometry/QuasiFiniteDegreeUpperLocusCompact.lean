/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.QuasiFiniteDegreeUpperLocusCompactAux

/-! # Quasi-compactness of upper fibre-degree loci

## References

* [Stacks Project, Tag 07RZ](https://stacks.math.columbia.edu/tag/07RZ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- On an affine open in the degree-at-least-r locus, the degree-at-least-(r+1)
locus is quasi-compact. The closed sublevel locus and the universal degree-r
criterion are explicit hypotheses, so this is only the descent step of the argument. -/
theorem isCompact_successor_degree_locus_inter_affine {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f] (hf : f.IsQuasiFinite)
    (r : ℕ) (W : S.Opens) (hW : IsAffineOpen W)
    (hclosed : IsClosed {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r})
    (hdegree : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔
        Set.range g ⊆ {s : S | (f.fiberToSpecResidueField s).finrankΓ = r})
    (hWge : ∀ s : S, s ∈ W → r ≤ (f.fiberToSpecResidueField s).finrankΓ) :
    IsCompact ({s : S | r + 1 ≤ (f.fiberToSpecResidueField s).finrankΓ} ∩
      (W : Set S)) := by
  obtain ⟨U, hUcompact, hUeq⟩ :=
    exists_compact_open_successor_degree_locus_inter_affine f hf r W hW hclosed hdegree hWge
  rw [← hUeq]
  exact hUcompact

end AlgebraicGeometry.Scheme.Hom
