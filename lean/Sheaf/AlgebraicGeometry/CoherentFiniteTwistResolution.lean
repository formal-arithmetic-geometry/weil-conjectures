module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Sheaf.AlgebraicGeometry.StandardProjCoherentSectionFiniteness
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.ProjSectionModuleReconstruction
import WeilConjectures.AlgebraicGeometry.ProjTildeFunctorial
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
import WeilConjectures.AlgebraicGeometry.ProjPolynomialTwistChart
import Sheaf.RingTheory.PolynomialGradedHilbertSyzygy
import Sheaf.AlgebraicGeometry.ProjGradedSheafificationExact
import WeilConjectures.AlgebraicGeometry.ProjFiniteTwistCoproductFractions
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExists
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Finite twist resolutions of coherent modules on projective space

Source: Stacks Project, Algebra, Tag 00OQ; Constructions, Tag 03GM;
Cohomology of Schemes, Tag 01YS
(blueprint: lem-sfb-projective-coherent-finite-twist-resolution).

The polynomial Proj model uses `Proj.twist` from
`def-weil-pbc-proj-twisting-sheaf`: the sheaf associated to `S(d)`. Its standard
chart frames have the transition rule of `def-pc-projective-space-twist`, whose
separate `ProjectiveSpace.twist` record is unchanged. A chain complex with zero
terms above `ℓ` records the finite exact sequence, including its left endpoint.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Proj

/-- Every coherent module on projective `n`-space over a field has a resolution
of length at most `n + 1` by finite sums of integer twists, with coherent terms.
Source: Stacks 00OQ, 03GM and 01YS
(blueprint: lem-sfb-projective-coherent-finite-twist-resolution).

Proof plan:
1. The field is Noetherian (`lem-weil-pbc-field-regular-ring`). By
`lem-sfb-standard-proj-coherent-section-finiteness`, the nonnegative twisted
section module is finite over the polynomial ring and Proj is Noetherian.
`pqf-lem-coherent-ft-locnoeth` gives quasi-coherence of the given coherent module.
2. `lem-sfb-proj-section-module-reconstruction` reconstructs the sheaf from the
all-integer section module. The inclusion of its nonnegative truncation induces
a map by `lem-sc-p1-proj-tilde-functorial`. Its degree-zero fractions on every
standard open are unchanged, so it is an isomorphism; use the fraction charts of
`def-weil-pbc-proj-twisting-sheaf` and the covering in
`lem-weil-pbc-proj-polynomial-twist-chart`.
3. Apply `lem-sfb-polynomial-graded-hilbert-syzygy` with `n + 1` variables to
obtain a graded resolution of length at most `n + 1` by finite shifted-free terms.
4. Apply `lem-sfb-proj-graded-sheafification-exact` to the short exact kernel
sequences and splice them. Functoriality identifies the composites with the
sheafified differentials; the zero module sheafifies to zero by its charts.
5. `lem-sc-proj-finite-twist-coproduct-fractions` and the chart uniqueness in
`lem-weil-pbc-proj-graded-module-sheaf-exists` identify each term with its sum
of Proj twists `S(d)`-tilde (`def-weil-pbc-proj-twisting-sheaf`). The chart bases
`x_i^d` have transition `(x_i/x_j)^d`, the gluing prescription of
`def-pc-projective-space-twist`, for all integer degrees, including negative ones.
6. Each term is locally free of finite rank, hence quasi-coherent and of finite
type (`pqf-def-coherent`), and therefore coherent by
`pqf-lem-coherent-ft-locnoeth`. Set `ℓ = n + 1`, allowing zero terminal terms.
For `G = 0`, alternatively set `ℓ = 0` and use an empty sum. For `n = 0`, the
same construction uses the one-variable polynomial ring and `ℓ ≤ 1`.
-/
theorem exists_coherent_finite_twist_resolution
    (k : Type u) [Field k] (n : ℕ)
    (G : (projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) k).Modules)
    (hG : RingedSpace.IsCoherent
      (projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) k).toRingedSpace G) :
    ∃ (ℓ : ℕ), ℓ ≤ n + 1 ∧
      ∃ (F : ChainComplex
          (projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) k).Modules ℕ)
        (π : F.X 0 ⟶ G) (w : F.d 1 0 ≫ π = 0),
        Epi π ∧ (ShortComplex.mk (F.d 1 0) π w).Exact ∧
        (∀ j : ℕ, F.ExactAt (j + 1)) ∧
        (∀ j : ℕ, ℓ < j → IsZero (F.X j)) ∧
        (∀ j : ℕ, j ≤ ℓ →
          RingedSpace.IsCoherent
            (projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) k).toRingedSpace
            (F.X j) ∧
          ∃ (r : ℕ) (d : Fin r → ℤ),
            Nonempty (F.X j ≅ ∐ (fun a : Fin r ↦
              @twist _ _ _ _ _
                (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k)
                MvPolynomial.gradedAlgebra (d a)))) := by
  sorry

end AlgebraicGeometry.Proj
