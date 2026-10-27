module

public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The simple-hyperplane criterion for perfect Lie algebras

Source: Milne, Algebraic Groups (2017), Section 22c, Lemma 22.40, printed pp. 476-477;
the DAG adapts its argument from algebraic groups to Lie modules over an arbitrary field
(blueprint: lem-sfb-perfect-lie-hyperplane-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace LieModule

/-- If every simple invariant hyperplane splits, all finite-dimensional modules of a perfect
Lie algebra have invariant complements to every invariant subspace.

Source: Milne, Algebraic Groups (2017), Lemma 22.40, printed pp. 476-477, adapted to Lie
modules (blueprint: lem-sfb-perfect-lie-hyperplane-criterion).

Proof: First, a one-dimensional representation has a linear character vanishing on every
bracket, since scalar endomorphisms commute. Perfectness makes this character zero.
Next prove splitting of every invariant hyperplane W in M by strong induction on dim M.
If W is zero, take M as complement; if W is simple, apply the hypothesis. Otherwise choose
a nonzero proper invariant A in W of maximal dimension, so W/A is simple. The quotient
M/A has smaller dimension, and induction splits its hyperplane W/A. Let P be the inverse
image of the resulting complementary line. Then P intersects W in A, M = W + P, and
A is a hyperplane in P. The short-exact dimension formula
(lem-trf-finite-dimensional-short-exact-dimension) gives dim P = dim A + 1 < dim M.
A second application of induction splits P = A + D; this D complements W in M.

For arbitrary U in V, the cases U = 0 and U = V are immediate. Otherwise consider
H = Hom_k(V,U) with (x.f)(v) = x.f(v) - f(x.v), the action of
lem-sfb-lie-linear-hom-action. This is finite-dimensional. Let E consist of maps restricting
to a scalar multiple of the identity on U, and K of maps restricting to zero. Both are
invariant, and x.E is contained in K. The scalar restriction map E to k has kernel K and is
surjective: a vector-space complement (lem-trf-vector-subspace-complement) gives a projection
onto U restricting to the identity. Thus K is a hyperplane in E. Split it by the preceding
induction, obtaining an invariant line D. Perfectness makes D trivial. A nonzero f in D
is therefore equivariant, and its scalar restriction a is nonzero. Then q = a⁻¹ f is an
equivariant retraction onto U. Its invariant kernel C complements U: each v is uniquely
q(v) + (v - q(v)), with the two terms in U and C respectively. -/
theorem exists_isCompl_of_perfect_of_simple_hyperplane
    (k : Type u) [Field k] (L : Type v) [LieRing L] [LieAlgebra k L]
    (_hperfect : LieAlgebra.derivedSeries k L 1 = ⊤)
    (hsplit : ∀ (M : Type (max u w)) [AddCommGroup M] [Module k M]
      [LieRingModule L M] [LieModule k L M] [FiniteDimensional k M]
      (W : LieSubmodule k L M), LieModule.IsIrreducible k L W →
      Module.finrank k (M ⧸ W.toSubmodule) = 1 →
      ∃ D : LieSubmodule k L M, IsCompl W D)
    (V : Type w) [AddCommGroup V] [Module k V]
    [LieRingModule L V] [LieModule k L V] [FiniteDimensional k V]
    (U : LieSubmodule k L V) : ∃ C : LieSubmodule k L V, IsCompl U C := by
  sorry

end LieModule
