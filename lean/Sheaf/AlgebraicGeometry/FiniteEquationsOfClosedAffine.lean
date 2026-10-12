module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-! Finite principal equations for a degree sublevel locus on an affine open. -/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- The degree sublevel locus restricted to an affine open is the zero locus of a finitely
    generated ideal.

Source: Stacks Project, More on Morphisms, Tag 07RZ, proof, second paragraph
(blueprint: lem-weil-pbc-finite-equations-of-isClosed-inter-affine).

Proof: identify the affine open with the spectrum of its coordinate ring. The closed sublevel
locus is represented by an ideal. Express that ideal as a filtered union of finitely generated
subideals and descend the finite locally free degree-r morphism to one such subideal. The
universal degree criterion then shows that this subideal has the same vanishing locus.
-/
theorem exists_finitely_generated_zeroLocus_ideal_degree_sublevel_inter_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] (hf : f.IsQuasiFinite)
    (r : ℕ) (W : S.Opens) (hW : IsAffineOpen W)
    (hclosed : IsClosed {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r})
    (hdegree : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔
        Set.range g ⊆ {s : S | (f.fiberToSpecResidueField s).finrankΓ = r})
    (hWge : ∀ s : S, s ∈ W → r ≤ (f.fiberToSpecResidueField s).finrankΓ) :
    ∃ I : Ideal Γ(S, W), I.FG ∧ ∀ s : S, s ∈ W →
      (s ∈ {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r} ↔
        s ∈ S.zeroLocus (U := W) I) := by
  sorry

/-- A finitely generated ideal on an affine open has finitely many principal equations.

Source: Stacks Project, More on Morphisms, Tag 07RZ, proof, second paragraph
(blueprint: lem-weil-pbc-finite-equations-of-finitely-generated-zeroLocus).

Proof: choose a finite generating set for the ideal; membership in its zero locus is equivalent
to avoiding every corresponding basic open.
-/
theorem exists_finite_equations_of_finitely_generated_zeroLocus
    {S : Scheme.{u}} {W : S.Opens} {I : Ideal Γ(S, W)} (hI : I.FG) :
    ∃ t : Finset Γ(S, W), ∀ s : S, s ∈ W →
      (s ∈ S.zeroLocus (U := W) I ↔ ∀ a ∈ t, s ∉ S.basicOpen a) := by
  obtain ⟨t, ht⟩ := hI
  refine ⟨t, ?_⟩
  intro s hs
  rw [← ht, Scheme.zeroLocus_span]
  simp only [Scheme.mem_zeroLocus_iff, Finset.mem_coe]

end AlgebraicGeometry.Scheme.Hom
