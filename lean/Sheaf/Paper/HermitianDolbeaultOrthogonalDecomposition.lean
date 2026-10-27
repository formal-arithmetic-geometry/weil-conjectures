module

public import Sheaf.Geometry.Manifold.HermitianDolbeaultData

/-!
# Orthogonal decomposition of smooth Dolbeault forms

Source: Kong, Notes on Complex Geometry, §6.2, Theorem 6.7, printed pp.23–24
(blueprint: lem-sfb-hermitian-dolbeault-orthogonal-decomposition).

The three spaces are the smooth harmonic kernel and the actual smooth images of the
Dolbeault operator and its formal adjoint. Orthogonality is for the metric integral pairing.
-/

@[expose] public section

universe u

open scoped Manifold ContDiff

namespace ComplexManifold

/-- On a compact Hermitian complex manifold without boundary, smooth forms of every
integer bidegree are the orthogonal direct sum of the harmonic, exact and coexact spaces.
Source: Kong, Notes on Complex Geometry, §6.2, Theorem 6.7, printed pp.23–24
(blueprint: lem-sfb-hermitian-dolbeault-orthogonal-decomposition).

Proof plan, following the four DAG steps:
1. For an invalid type all spaces vanish. The empty manifold is immediate. In complex
   dimension zero the base is finite discrete, only degree zero survives, the differentials
   vanish, and all degree-zero forms are harmonic. Otherwise fix a valid type.
2. The node lem-sfb-dolbeault-laplacian-elliptic gives ellipticity of the smooth Laplacian.
   Adjointness makes it self-adjoint, also for the real part of the pairing. Apply
   lem-sfb-elliptic-smooth-fredholm-decomposition to the realified type bundle, with the
   positive real metric and complex orientation. Every smooth form is h + Δw with h harmonic
   and w smooth. Expanding Δw gives actual smooth primitives D*w and Dw in the adjacent types.
3. Pair Δh = 0 with h. Adjointness gives the sum of the squared norms of Dh and D*h, so both
   are zero. A nonzero smooth form has positive pointwise norm on a coordinate neighborhood,
   which has positive metric volume; hence zero integral norm implies the form is zero.
   Adjointness now makes h orthogonal to both images for the complex pairing.
4. Exact and coexact forms are orthogonal because D² = 0. The decomposition in step 2 proves
   the subspace equality. Pair a zero sum of its three components separately with each
   component: orthogonality forces all three norms, and hence all components, to vanish.
   Subtraction proves uniqueness. No image closure or completeness assumption is used. -/
theorem hermitian_dolbeault_orthogonal_decomposition
    (n : ℕ) (M : Type u) [TopologicalSpace M] [ChartedSpace (Model n) M]
    [IsManifold (𝓘(ℂ, Model n)) ∞ M] [T2Space M]
    [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    (g : HermitianMetric n M) (μ : MetricVolume g) (D : DolbeaultOperators g μ)
    (p q : ℤ) :
    (D.harmonic p q ⊔ D.exact p q ⊔ D.coexact p q = typeForms p q) ∧
    (∀ (h : D.harmonic p q) (a : D.exact p q), l2Pair g μ h.val a.val = 0) ∧
    (∀ (h : D.harmonic p q) (b : D.coexact p q), l2Pair g μ h.val b.val = 0) ∧
    (∀ (a : D.exact p q) (b : D.coexact p q), l2Pair g μ a.val b.val = 0) ∧
    ∀ α : typeForms (n := n) (M := M) p q,
      ∃! c : D.harmonic p q × D.exact p q × D.coexact p q,
        α.val = c.1.val + c.2.1.val + c.2.2.val := by
  sorry

end ComplexManifold
