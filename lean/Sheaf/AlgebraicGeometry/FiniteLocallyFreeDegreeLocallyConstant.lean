import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Locally constant fibre degree of a finite locally free morphism

Source: literature/stacks-project/morphisms.tex, Section 02K9, Definition 02KA
and Lemma 04MH (blueprint: lem-weil-pbc-finite-locally-free-degree-locally-constant).
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- For a finite locally free morphism, the fibre dimension is finite and locally constant;
the clopen fibres give the equivalent decomposition into constant-degree restrictions.
Source: Stacks Morphisms, Definition 02KA and Lemma 04MH
(blueprint: lem-weil-pbc-finite-locally-free-degree-locally-constant).
Step 1 applies the finite-flat rank statement `lem-weil-pbc-finite-flat-rank-iso` to identify
this dimension with the finite rank and obtain local constancy. Step 2 takes the clopen fibres
of the locally constant function and restricts `f` to each one, preserving finite, flat, and
locally finitely presented. Step 3 identifies these fibres and restricted degrees with the
asserted equivalent formulation.
-/
theorem finiteLocallyFree_fiberDimension_isLocallyConstant
    {X S : Scheme.{u}} (f : X ⟶ S) [f.IsFiniteLocallyFree] :
    let δ : S → ℕ := fun s => (f.fiberToSpecResidueField s).finrankΓ
    (∀ s : S, Module.Finite (S.residueField s) Γ(f.fiber s, ⊤)) ∧
      IsLocallyConstant δ ∧
      (∀ d : ℕ, IsClopen (δ ⁻¹' {d})) ∧
      (∃ U : ℕ → S.Opens,
        (∀ d : ℕ, ∀ s : S, s ∈ U d ↔ δ s = d) ∧
          (∀ d : ℕ, (f ∣_ U d).IsFiniteLocallyFreeOfDegree d)) := by
  sorry

end AlgebraicGeometry
