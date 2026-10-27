module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.RelativeTorus
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup

/-! # Finite torsion detects the normalizer of a split torus

Source: Conrad, *Reductive group schemes*, Theorem 2.3.1 proof, printed p.68;
Proposition 2.1.2 proof, pp.57-58, and Example 2.1.9, p.62.
(blueprint: lem-sfb-split-torus-finite-torsion-normalizer-detection).

Subgroups are evaluated on every test scheme over W. For a test map f : V → W,
composition with f restricts g to V, and composition with i includes T(V) in G(V).
The n-torsion subfunctor consists exactly of t with t ^ n = 1; under the splitting
these are tuples of units whose nth powers are one, represented by the Laurent
algebra quotient A[t₁⁺⁻¹, ..., tᵣ⁺⁻¹]/(t₁ⁿ - 1, ..., tᵣⁿ - 1).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A single positive torsion level detects the normalizer of a closed split torus,
as subgroup functors after every base change. The same n precedes all W and g.

Source: Conrad, *Reductive group schemes*, Theorem 2.3.1 proof, printed p.68;
Proposition 2.1.2 proof, pp.57-58, and Example 2.1.9, p.62.
(blueprint: lem-sfb-split-torus-finite-torsion-normalizer-detection).

Proof (the accepted split-coordinate argument, valid over every ring):
1. Write G = Spec B and T = Spec L, where L is the Laurent algebra on r
   variables over A. The finite presentation of B follows from
   lem-weil-pbc-lfp-affine-opens-finite-presentation. The affine adjunction
   lem-a1-locally-ringed-space-affine-adjunction identifies maps to Spec L on
   every scheme with r-tuples of units. The closed inclusion gives B → L
   surjective; denote its kernel by I.
2. Choose A[x₁,...,x_d] → B surjective. Present L using variables t_i,u_i
   and relations t_i*u_i - 1. By
   lem-weil-pbc-finite-presentation-surjection-kernel-fg the composite
   polynomial surjection to L has finitely generated kernel. Its generators
   descend to finitely many generators f_j of I in B.
3. Universal conjugation G × T → G gives B → B[t₁⁺⁻¹,...,tᵣ⁺⁻¹]. The
   affine adjunction identifies this spectrum with G × T on all test schemes.
   Expand the image of each f_j as a finite sum of b_ju*t^u. Specializing B
   along any g in G(R) gives the conjugation polynomials over R.
4. Bound all coordinates of all exponents in these finitely many supports
   by M ≥ 0 and take n = 2*M + 2. Reduction modulo n is injective on their
   union: a coordinate difference divisible by n has absolute value < n.
5. Apply lem-sfb-subgroup-algebra-coset-presentation to (Z/nZ)^r and its
   zero subgroup. The torsion quotient of the Laurent algebra over any R is
   R[(Z/nZ)^r]. Its indexed monomials are a basis, by
   def-sfb-ring-diagonalizable-group. On the chosen supports reduction modulo
   n therefore detects vanishing of every coefficient, also over the zero ring.
6. If g normalizes T[n] over R, its conjugation of T[n] lands in T, so all
   f_j vanish in the torsion quotient. Step 5 forces all specialized b_ju
   to vanish. Conjugation by g thus carries T into T. The same argument for
   g inverse, using the same n, gives the inverse factorization and hence
   equality of subgroup functors on every R-scheme.
7. Conversely, conjugation preserving T preserves its n-torsion: for every
   test scheme, (g*t*g inverse)^n = g*t^n*g inverse. Apply this also to
   g inverse to obtain equality, rather than just containment.
8. For arbitrary W apply steps 6-7 on every affine open of W. The factors
   agree on overlaps because the subgroup inclusion is monic. Glue them by
   lem-weil-pbc-scheme-morphism-gluing; their composites are identities by
   uniqueness. The original n works on every W and every further base change.
   For A = 0 every test scheme is empty; for r = 0 the subgroup is the identity.
   Neither reducedness, a Noetherian hypothesis nor invertibility of n is used. -/
theorem split_torus_exists_finite_torsion_normalizer_detection
    (A : Type u) [CommRing A] (G T : Over (Spec (.of A))) [GrpObj G] [GrpObj T]
    [Smooth G.hom] [IsAffineHom G.hom] [LocallyOfFinitePresentation G.hom]
    [QuasiCompact G.hom] [QuasiSeparated G.hom]
    (r : ℕ) (hT : Nonempty (yonedaGrpObj T ≅ relativeSplitTorusFunctor (Spec (.of A)) r))
    (i : T ⟶ G) [IsMonHom i] [IsClosedImmersion i.left] :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (W : Over (Spec (.of A))) (g : W ⟶ G),
      (∀ (V : Over (Spec (.of A))) (f : V ⟶ W),
        Set.range (fun t : V ⟶ T ↦ (f ≫ g) * (t ≫ i) * (f ≫ g)⁻¹) =
          Set.range (fun t : V ⟶ T ↦ t ≫ i)) ↔
      (∀ (V : Over (Spec (.of A))) (f : V ⟶ W),
        (fun t : V ⟶ T ↦ (f ≫ g) * (t ≫ i) * (f ≫ g)⁻¹) '' {t | t ^ n = 1} =
          (fun t : V ⟶ T ↦ t ≫ i) '' {t | t ^ n = 1}) := by
  sorry

end AlgebraicGeometry
