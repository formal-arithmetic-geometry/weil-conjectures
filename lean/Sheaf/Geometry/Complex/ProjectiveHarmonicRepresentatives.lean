module

public import Sheaf.Geometry.Complex.ProjectiveDolbeaultData
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.Paper.HermitianDolbeaultOrthogonalDecomposition

/-! # Harmonic representatives on smooth complex projective schemes

Source: Popa, Kodaira dimension of algebraic varieties, proof of Theorem 1.6.6,
printed pp.26--27 (blueprint: lem-sfb-projective-harmonic-representatives).

The equipped analytification is presented by its finitely many connected components.
No common dimension or nonemptiness is imposed. All operators and classes below are
those on actual smooth complex differential forms in the imported definitions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace ComplexManifold

/-- Every Dolbeault class has a harmonic representative, and every harmonic form is
closed for the analytic exterior derivative, including on the empty scheme.
Source: Popa, Theorem 1.6.6 proof, pp.26--27; Kong, Theorem 6.7 and Proposition 6.12
(blueprint: lem-sfb-projective-harmonic-representatives).

Proof plan, following all four DAG steps:
1. By lem-sfb-algebraic-dolbeault-derivative-comparison the analytification is the
   finite disjoint union of compact components in the presentation. Their dimensions
   may differ. Differentials, adjoints, and Laplacians act componentwise: integration
   on the disjoint union is the sum of the component integrals.
2. On each component choose a closed smooth representative beta. Apply
   lem-sfb-hermitian-dolbeault-orthogonal-decomposition to write beta = h+dbar u+dbar* v.
   Pair the harmonic equation with h: the sum of the squared norms of dbar h and
   dbar* h is zero, hence dbar h=0. The residual gamma=dbar* v is closed. Adjointness
   gives its squared norm as <v,dbar gamma>=0, hence gamma=0. Thus beta-h=dbar u.
   Zero integral norm implies zero smooth form, since a nonzero value persists on a
   coordinate neighborhood of positive metric volume.
3. For every harmonic alpha, lem-sfb-kahler-laplacian-identity gives
   Delta_d alpha=2 Delta_dbar alpha=0. The de Rham adjoint identity makes this the sum
   of the squared norms of d alpha and d* alpha. Both vanish, so d alpha=0.
4. Assemble the component representatives and primitives into families. Their
   difference is a global boundary, giving the same quotient class. Above a component's
   dimension the type space is zero. In dimension zero all derivatives vanish.
   For zero components all form and cohomology spaces are zero and the zero form suffices. -/
theorem projective_harmonic_representatives {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℂ))) [Smooth f] [IsProjective f]
    (A : SmoothAnalytic.Data f) (P : ProjectiveDolbeaultData A) (p q : ℕ) :
    (∀ b : P.Cohomology p q, ∃ α : P.cycles p q,
      P.classOf p q α = b ∧ ∀ i, (P.operators i).laplacian (α.val i) = 0) ∧
    (∀ α : P.Forms,
      (∀ i, α i ∈ (P.operators i).harmonic p q) →
        ∀ i, (P.operators i).dbar (α i) + (P.operators i).del (α i) = 0) := by
  sorry

end ComplexManifold
