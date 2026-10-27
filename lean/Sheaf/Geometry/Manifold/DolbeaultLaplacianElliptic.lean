module

public import Sheaf.Geometry.Manifold.FormDifferentialExpressions
import Sheaf.Analysis.Calculus.CoordinateWeightedAdjoint
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Formal adjoint and ellipticity of the Dolbeault Laplacian

Source: Kong, Notes on Complex Geometry, §6.1 Lemma 6.2 and §6.2 Lemma 6.4,
printed pp.21 and 23 (blueprint: lem-sfb-dolbeault-laplacian-elliptic).

The canonical operators exist on the concrete space of smooth forms. Their coordinate
expressions have smooth coefficients, and ellipticity is tested on the actual type fibre,
including the underlying real fibre, using the highest-order coefficients alone.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped Manifold ContDiff

namespace ComplexManifold

/-- The Dolbeault formal adjoint exists with smooth coefficients of order at most one;
its Laplacian has smooth coefficients of order at most two and an invertible degree-two
symbol on both the complex and real type fibres at every nonzero real covector.
Source: Kong, Notes on Complex Geometry, §6.1 Lemma 6.2 and §6.2 Lemma 6.4,
printed pp.21 and 23 (blueprint: lem-sfb-dolbeault-laplacian-elliptic).

Proof plan, following all six DAG steps:
1. In holomorphic coordinates, `dbar` differentiates coefficients by
   `(∂x_j + i ∂y_j)/2`. Its first symbol is left exterior multiplication by `ξ^(0,1)`;
   the sign from moving past the `(1,0)` factors is included in left multiplication.
2. Apply `lem-sfb-coordinate-weighted-adjoint` with the induced Hermitian Gram matrices
   and metric volume density. Its first coefficients give the negative fibre adjoint
   of the first symbol of `dbar`. Inversion of positive Gram matrices preserves smoothness.
3. Choose a finite holomorphic coordinate cover and use
   `lem-sfb-smooth-subordinate-partition`, namely
   `SmoothPartitionOfUnity.exists_isSubordinate`. Sum the local adjoints applied to the
   partition multiples, extending by zero. Closed supports inside the charts make these
   extensions smooth. Integration by parts proves the global adjunction, and derivatives
   of cutoffs contribute only terms of order zero. The symbol is the negative adjoint.
4. The difference of two adjoints pairs to zero with every smooth form. Pair it with
   itself; positivity on a coordinate ball makes zero integral norm imply it vanishes.
   This proves uniqueness. At missing adjacent types the spaces and maps are zero.
5. For a nonzero real covector, `η = ξ^(0,1)` is nonzero. An orthonormal basis starting
   with `η/‖η‖` shows that exterior multiplication and its adjoint have anticommutator
   `‖η‖² id` in every type, also when `q = 0` or `q = n`.
6. The product rule makes the degree-two symbol of `D D* + D* D` equal to
   `-‖η‖² id`; derivatives of coefficients have lower order. Its inverse is
   `-‖η‖⁻² id`. Restricting scalars preserves these inverse maps, proving real ellipticity.
-/
theorem dolbeault_laplacian_elliptic
    (n : ℕ) (hn : 1 ≤ n) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (Model n) M]
    [IsManifold (𝓘(ℂ, Model n)) ∞ M] [T2Space M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (g : HermitianMetric n M) (μ : MetricVolume g) :
    ∃ D : DolbeaultOperators g μ, ∀ (p q : ℤ),
      0 ≤ p → p ≤ n → 0 ≤ q → q ≤ n →
      HasFormDifferentialOrder 1 p (q + 1) p q D.adjoint ∧
      (∀ (α : typeForms (n := n) (M := M) p q)
          (η : typeForms (n := n) (M := M) p (q + 1)),
        l2Pair g μ (D.dbar α.val) η.val = l2Pair g μ α.val (D.adjoint η.val)) ∧
      (∀ S : smoothForms (n := n) (M := M) →ₗ[ℂ] smoothForms (n := n) (M := M),
        (∀ η : typeForms (n := n) (M := M) p (q + 1), S η.val ∈ typeForms p q) →
        (∀ (α : typeForms (n := n) (M := M) p q)
            (η : typeForms (n := n) (M := M) p (q + 1)),
          l2Pair g μ (D.dbar α.val) η.val = l2Pair g μ α.val (S η.val)) →
        ∀ η : typeForms (n := n) (M := M) p (q + 1), S η.val = D.adjoint η.val) ∧
      HasFormDifferentialOrder 2 p q p q D.laplacian ∧
      IsFormElliptic 2 p q D.laplacian := by
  sorry

end ComplexManifold
