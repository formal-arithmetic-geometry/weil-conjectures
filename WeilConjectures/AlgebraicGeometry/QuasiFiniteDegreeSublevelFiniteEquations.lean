/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.FiniteEquationsOfClosedAffine

/-! # Finite equations for the closed fibre-degree sublevel locus

## References

* [Stacks Project, Tag 07RZ](https://stacks.math.columbia.edu/tag/07RZ)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- The closed degree-at-most-r locus on an affine open has finitely many equations. -/
theorem exists_finite_equations_degree_sublevel_inter_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] (hf : f.IsQuasiFinite)
    (r : ℕ) (W : S.Opens) (hW : IsAffineOpen W)
    (hclosed : IsClosed {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r})
    (hdegree : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔
        Set.range g ⊆ {s : S | (f.fiberToSpecResidueField s).finrankΓ = r})
    (hWge : ∀ s : S, s ∈ W → r ≤ (f.fiberToSpecResidueField s).finrankΓ) :
    ∃ t : Finset Γ(S, W), ∀ s : S, s ∈ W →
      ((f.fiberToSpecResidueField s).finrankΓ ≤ r ↔ ∀ a ∈ t, s ∉ S.basicOpen a) := by
  obtain ⟨I, hI, hIZ⟩ := exists_finitely_generated_zeroLocus_ideal_degree_sublevel_inter_affine
    f hf r W hW hclosed hdegree hWge
  obtain ⟨t, ht⟩ := exists_finite_equations_of_finitely_generated_zeroLocus hI
  refine ⟨t, fun s hs ↦ ?_⟩
  change s ∈ {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r} ↔ _
  exact (hIZ s hs).trans (ht s hs)

end AlgebraicGeometry.Scheme.Hom
