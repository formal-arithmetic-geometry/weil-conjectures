module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra
import WeilConjectures.RingTheory.FiniteRingMapQuasiFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Finite projective envelopes

Source: Orgogozo, Proposition 2.3, proof, printed p. 4
(blueprint: lem-trf-finite-projective-envelope)
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/--
Source: Orgogozo, Proposition 2.3, proof, printed p. 4
(blueprint: lem-trf-finite-projective-envelope).

Proof:
1. Choose an affine presentation of `B` and let `Q = ℙ^d_B`. The standard projective
   charts cover `Q`, with the zero chart identified with `𝔸^d_B`; the structure map
   `Q ⟶ B` is proper. Hence `Q` is quasi-compact and quasi-separated. The affine
   chart is quasi-compact, so its open immersion into `Q` is quasi-compact by
   `lem-weil-pbc-qcqs-morphism-permanence`.
2. Compose the given finite map with this chart immersion. The source is affine,
   so the composite is separated. The finite map is quasi-finite and of finite
   type, and the chart immersion is quasi-compact and of finite type; thus the
   composite is finite type and quasi-finite, including the affine local
   quasi-finiteness condition.
3. Apply `thm-pqf-zmt-factorization` to obtain a quasi-compact open immersion
   `j : T ⟶ P` and a finite map `r : P ⟶ Q` with `j ≫ r` equal to the composite.
   Set `p = r ≫ q`. Finite maps are proper, and properness is stable under
   composition, so `p` is proper and the structural equation follows.
4. The ample invertible sheaf on `Q`, finite-map projectivity, conversion from
   projective-bundle projectivity to H-projectivity, and H-projective composition
   show that `p` is projective in the convention of `def-pc-projective-morphism`.
5. For a point `b : B`, base change identifies the fibre of `Q` with projective
   space over the residue field. Its standard affine charts cover the fibre of
   `P`; each chart is affine with coordinate ring finite over a polynomial ring
   in `d` variables.
6. The finite polynomial-algebra dimension bound gives dimension at most `d` on
   every chart. Scheme sobriety supplies the hypotheses of the open-cover dimension
   lemma, which gives the same bound for the whole fibre, including an empty fibre.
   The argument also covers zero algebras and non-surjective finite maps.
-/
theorem exists_finite_projective_envelope
    {B T : Scheme.{u}} [IsAffine B] (d : ℕ)
    (h : T ⟶ 𝔸(ULift.{u} (Fin d); B)) [IsFinite h] :
    ∃ (P : Scheme.{u}) (j : T ⟶ P) (p : P ⟶ B),
      IsOpenImmersion j ∧ IsProjective p ∧ IsProper p ∧
        j ≫ p = h ≫ (𝔸(ULift.{u} (Fin d); B) ↘ B) ∧
        ∀ b : B, topologicalKrullDim (p.fiber b) ≤ (d : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
