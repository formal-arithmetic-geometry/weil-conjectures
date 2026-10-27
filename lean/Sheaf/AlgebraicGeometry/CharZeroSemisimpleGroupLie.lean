module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.RepresentationTheory.CharZeroDifferentiationHom
public import Mathlib.Algebra.Lie.Semisimple.Basic

import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket
import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange
import Sheaf.AlgebraicGeometry.SmoothAmbientNormalityGeometric

/-! # The Lie algebra of a semisimple group in characteristic zero

Source: Milne, Algebraic Groups (2017), §22c, printed p.476, and Theorem 22.53,
first assertion, printed p.481 (blueprint: lem-sfb-char-zero-semisimple-group-lie).

The semisimple group predicate includes smoothness, connectedness, affineness,
finite type, and triviality of every smooth connected solvable normal closed subgroup.
The Lie algebra is the existing canonical tangent Lie algebra, with the bracket identified
by `charZero_differentiation_hom`. Semisimplicity here means trivial solvable radical,
as in the recorded definition node `def-wf-semisimple-lie-algebra`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The canonical tangent Lie algebra of a semisimple group over an algebraically closed
field of characteristic zero has no nonzero solvable Lie ideal.
Source: Milne, Algebraic Groups (2017), §22c, printed p.476, and Theorem 22.53,
first assertion, printed p.481 (blueprint: lem-sfb-char-zero-semisimple-group-lie).

Proof:
1. Apply lem-sfb-central-torus-faithful-weight-blocks with the trivial central torus
   to embed G in GL(V). The identity is closed since the counit is surjective.
   The tangent description of def-wf-lie-algebra-derivation identifies Lie(G) with
   the matrices X for which 1 + epsilon X lies in G over the dual numbers.
   By lem-sfb-char-zero-differentiation-hom the differential preserves the canonical
   bracket, which in this matrix realization is the matrix commutator.
2. For a commutative Lie ideal n, the differential of the adjoint action preserves n.
   The stable-subspace clause of sk-p-comparison makes n rationally G-stable.
   Restriction therefore defines a group-scheme homomorphism r : G -> GL(n).
3. Define H = ker r by the equations r(g)_ij = delta_ij. It is a normal closed
   affine finite-type subgroup. The dual-number calculation gives
   Lie(H) = h = {x | [x,n] = 0}, and commutativity gives n contained in Z(h).
4. Cartier smoothness (lem-sfb-char-zero-affine-group-smooth) makes H smooth.
   Use lem-sfb-group-neutral-component-translates to form its smooth connected
   identity component H0, with the same tangent Lie algebra h. The closed centre
   Z(H0) from lem-sfb-affine-group-centre-base-change is commutative and smooth
   by Cartier; its identity component C is smooth, connected, closed and solvable.
5. Every rational conjugation preserves H, then H0, its centre, and C.
   By lem-sfb-smooth-ambient-normality-geometric, C is scheme-theoretically normal
   in G. Semisimplicity of G forces C to be the trivial group scheme.
6. The centre clause of sk-p-comparison identifies Lie(C) with Z(h).
   Hence Z(h) = 0, so n = 0. Every commutative Lie ideal of Lie(G) vanishes.
7. For any solvable ideal I, every term of its derived series is an ideal of Lie(G)
   by Jacobi. If I were nonzero, its last nonzero derived term would be a nonzero
   commutative ideal, contradicting step 6. Thus every solvable ideal is zero.
   By def-wf-semisimple-lie-algebra, equivalently
   LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals, this is the conclusion.
-/
theorem semisimpleGroupScheme_lie_hasTrivialRadical
    (F : Type u) [Field F] [IsAlgClosed F] [CharZero F]
    (G : Scheme.{u}) [G.Over (Spec (.of F))]
    [GrpObj (G.asOver (Spec (.of F)))]
    (hG : IsSemisimpleGroupScheme (G.asOver (Spec (.of F)))) :
    LieAlgebra.HasTrivialRadical F (GrpObj.Lie (G.asOver (Spec (.of F)))) := by
  sorry

end AlgebraicGeometry
