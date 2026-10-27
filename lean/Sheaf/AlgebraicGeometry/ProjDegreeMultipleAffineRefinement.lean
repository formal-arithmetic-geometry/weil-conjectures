module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Sheaf.AlgebraicGeometry.ProjStandardOpenBasis

/-!
# Degree-multiple affine standard-open refinements of Proj

Source: Stacks Project, Constructions, Tags 01MW (proof of (6)--(7)) and 01MB;
Algebra, Tag 00JP (5) (blueprint: lem-trf-proj-degree-multiple-affine-refinement).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Proj

/-- On every open subscheme of Proj, standard opens of positive degree divisible by a fixed
positive integer form an affine basis. The local refinement can be chosen by taking the
specified power of a positive-degree homogeneous element. Its canonical map to the spectrum
of the degree-zero homogeneous localization is an isomorphism.

Source: Stacks Project, Tags 01MW (proof of (6)--(7)), 01MB, and 00JP (5)
(blueprint: lem-trf-proj-degree-multiple-affine-refinement).

Proof:
1. The open immersion `U.ι` identifies each open neighbourhood `N` in `U` with its open
image in Proj (`def-weil-open-immersion`). Apply the positive-degree standard-open basis
`lem-sc-proj-standard-open-basis` there to find `q > 0` and `g ∈ 𝒜 q` whose standard open
contains the chosen point and lies in that image.
2. Graded multiplication places `g ^ d` in `𝒜 (q * d)`. Since `d > 0`, primality gives
`g ^ d ∈ 𝔭` if and only if `g ∈ 𝔭` for every homogeneous prime point of Proj
(`def-pc-proj`). Thus the two standard opens agree, including their restricted scheme
structures, and retain the inclusions of Step 1.
3. Apply `prop-nagata-proj-standard-open` to `g` of positive degree `q`: its canonical
`basicOpenToSpec` map to `Spec (HomogeneousLocalization.Away 𝒜 g)` is an isomorphism,
and the common standard open is affine.
4. Every homogeneous element of degree `n * d`, with `n > 0`, has positive degree, so its
standard open is affine by `prop-nagata-proj-standard-open`. When this whole open lies in
`U`, its preimage under `U.ι` is the same open subscheme, hence affine. Steps 1--2 produce
such a member inside each neighbourhood, with `n = q`, proving the basis assertion.
No finite cover or quasi-compactness assumption is used. -/
theorem degreeMultiple_affine_refinement
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) (U : (Proj 𝒜).Opens) :
    (∀ (x : U.toScheme) (N : U.toScheme.Opens), x ∈ N →
      ∃ (q : ℕ) (g : A), 0 < q ∧ g ∈ 𝒜 q ∧ g ^ d ∈ 𝒜 (q * d) ∧
        U.ι x ∈ basicOpen 𝒜 (g ^ d) ∧
        basicOpen 𝒜 (g ^ d) = basicOpen 𝒜 g ∧
        basicOpen 𝒜 g ≤ U.ι ''ᵁ N ∧
        IsAffineOpen (basicOpen 𝒜 g) ∧ IsIso (basicOpenToSpec 𝒜 g)) ∧
    TopologicalSpace.Opens.IsBasis
      {V : U.toScheme.Opens | ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 (n * d) ∧
        basicOpen 𝒜 f ≤ U ∧ V = U.ι ⁻¹ᵁ basicOpen 𝒜 f} ∧
    (∀ (n : ℕ) (f : A), 0 < n → f ∈ 𝒜 (n * d) → basicOpen 𝒜 f ≤ U →
      IsAffineOpen (U.ι ⁻¹ᵁ basicOpen 𝒜 f)) := by
  sorry

end AlgebraicGeometry.Proj
