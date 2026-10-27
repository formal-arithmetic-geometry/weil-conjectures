module

public import Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.StrictCodegreePolygonGap

/-! # Uniform Hilbert stability of high-degree complete series on smooth curves

Source: Morrison, arXiv:0810.2340, Section 2.4, Theorem 5, printed pp.10--11.
(blueprint: lem-sfb-smooth-curve-high-degree-hilbert-stability)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- Complete high-degree series have stable Hilbert points in a degree bounded only
by genus and degree. The coordinate sum is the actual evaluation of the chosen
coordinates, so its bijectivity expresses precisely completeness of the series.
The equality of ideal sheaves identifies the Hilbert point with the given embedding.
The parameter n writes the number of coordinates as r = n + 2.
Source: Morrison, Section 2.4, Theorem 5, pp.10--11; Section 2.1 for linearization.
(blueprint: lem-sfb-smooth-curve-high-degree-hilbert-stability)

Proof plan, following the six DAG steps:
1. Put N=d+1-g. Completeness gives h⁰(L)=N and the embedding gives surjective
   evaluation. For every full flag V_i of dimension N-i apply
   lem-sfb-linear-series-degree-dimension-bound to its generated invertible image A_i.
   Write a_i=deg(A_i) and e_i=d-a_i. Then 0≤a_i≤d and
   N-i≤max(a_i+1-g,a_i/2+1).
2. The complete space generates L, giving e_0=0. The last, one-dimensional
   subspace generates a trivial invertible image, giving e_(N-1)=d. All codegrees
   lie between zero and d. These are the endpoint clauses of that same dependency.
3. Here N≥4 and 1<α=d/(N-1)<2. The Riemann--Roch branch gives e_i≤i<αi
   at interior indices. The Clifford branch gives e_i≤d-2(N-1)+2i; subtracting
   αi gives (2-α)(i-(N-1))<0. Thus every interior codegree satisfies e_i<αi.
4. Apply lem-sfb-strict-codegree-polygon-gap to obtain η(N,d)>0, uniform over
   all these integral codegrees and all decreasing normalized real weights.
   Every flag therefore satisfies B(e,w)≤2d/N-η(N,d), uniformly over all fields.
5. Apply lem-sfb-uniform-gieseker-codegree-criterion with ε=η(N,d) and
   V=H⁰(C,L). It gives M₀(g,d,N,η) and stable SL_N Hilbert points for every
   m≥M₀, with polynomial dm+1-g. Both N and η depend only on g,d.
6. Increase M₀ to the Hilbert embedding threshold in
   lem-sfb-hilbert-plucker-pgl-linearization. Its equality of SL and PGL stable
   loci identifies the conclusion with stability for the specified PGL-linearized
   rth determinant power. This holds even when the characteristic divides r.
-/
theorem exists_uniform_smooth_curve_high_degree_hilbert_stability
    (g d : ℕ) (hg : 2 ≤ g) (hd : 2 * g + 1 ≤ d) :
    ∃ M : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (C : Scheme.{u}) [C.Over (Spec (.of k))]
      [IsConnectedCurve (C ↘ Spec (.of k))]
      [Smooth (C ↘ Spec (.of k))] [IsHProjective (C ↘ Spec (.of k))]
      (L : C.Modules) [L.IsInvertible],
      C.arithmeticGenus k = g → L.degree k = (d : ℤ) →
      ∀ (n : ℕ), n + 2 + g = d + 1 →
      ∀ (i : C ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k))),
        IsClosedImmersion i →
        i ≫ (ℙ(HilbertPlucker.Coordinates n; Spec (.of k)) ↘ Spec (.of k)) =
          (C ↘ Spec (.of k)) →
        ∀ e : (Scheme.Modules.tensorPullback i).obj
            (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) 1) ≅ L,
          Function.Bijective
            (fun a : HilbertPlucker.Coordinates n → k ↦
              ∑ j : HilbertPlucker.Coordinates n,
                (C ↘ Spec (.of k)).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv (a j)) •
                  e.hom.app ⊤
                    (((Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app
                      (ProjectiveSpace.twist (HilbertPlucker.Coordinates n)
                        (Spec (.of k)) 1)).app ⊤
                          (ProjectiveSpace.twistOneSection
                            (HilbertPlucker.Coordinates n) (Spec (.of k)) j))) →
          ∀ m : ℕ, M ≤ m →
            ∃ (P : NumericalHilbertPolynomial)
              (_ : P.1 = Polynomial.C (d : ℚ) * Polynomial.X +
                Polynomial.C (1 - (g : ℚ)))
              (D : HilbertPlucker.Hilbert k n P) (E : HilbertPlucker.Presentation D m)
              (x : PGLLinearization.fieldTest k k ⟶ D.H),
              D.ideal.comap (ProjectiveSpace.map (HilbertPlucker.Coordinates n) x.left) =
                i.ker ∧ E.pgl_line.IsStable k x := by
  sorry

end AlgebraicGeometry
