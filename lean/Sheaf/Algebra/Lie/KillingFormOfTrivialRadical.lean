module

public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.Algebra.Lie.Solvable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import WeilConjectures.RepresentationTheory.CompositionSeries
import WeilConjectures.Mathlib.Algebra.Lie.CartanCriterion

/-!
# The Killing form and derived algebra when the radical vanishes

Source: the current blueprint, sec-algebraic-groups-lie-algebras,
`sk-lem-walg-killing`, with the characteristic-zero scalar-extension repair
recorded in the DAG (blueprint: sk-lem-walg-killing).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace LieAlgebra

/-- A finite-dimensional Lie algebra over any characteristic-zero field with zero
solvable radical has nondegenerate Killing form and equals its derived algebra.
Here `killingForm k g x y` is `tr (ad x ∘ ad y)`, and `derivedSeries k g 1`
is the linear span of all brackets.

Source: the current blueprint, sec-algebraic-groups-lie-algebras,
`sk-lem-walg-killing`, and its reviewed scalar-extension repair
(blueprint: sk-lem-walg-killing).

Proof plan:
1. Let K be the kernel of the Killing form B. Invariance and symmetry make K an
   ideal. Restriction to an ideal identifies its Killing form with the restriction
   of B (`lem-ag-killing-form-identities`), so the Killing form of K is zero.
2. Choose an algebraic closure E of k (`def-weil-algebraic-closure`) and form
   H = E ⊗[k] K with the tensor-product Lie bracket. A finite basis extends to a
   finite basis over E, satisfying the coefficient conventions of `det-d-linear`.
   On pure tensors, ad(1 ⊗ x) is the base change of ad(x), including products.
   The trace identity of `lem-ag-trace-solvability-scalar-extension` makes the
   Killing form of H zero on pure tensors, hence everywhere by bilinearity.
   For the adjoint image A, brackets and linear combinations lift, so [A,A] is
   the image of [H,H]. Thus the trace of XY vanishes for X in [A,A], Y in A.
   The trace criterion `sk-lem-walg-trace-criterion` makes A solvable.
3. The adjoint kernel is the centre of H. Images of successive derived terms
   lie in the corresponding derived terms of A (`def-wf-lie-algebra`). Thus a
   derived term of H is central, and the next is zero. Descend solvability to K
   using `lem-ag-trace-solvability-scalar-extension`. The solvable ideal K lies
   in the radical (`def-wf-lie-radical-centre`), which is zero; hence B is
   nondegenerate.
4. Put D = [g,g]. Invariance gives B(x,[y,z]) = B([x,y],z). For z in the
   orthogonal complement of D this is zero for all x,y; symmetry and
   nondegeneracy imply [y,z] = 0. Conversely, central z is orthogonal to all
   brackets, hence their span. Thus D's orthogonal complement is the centre.
5. The centre is an abelian ideal by Jacobi, hence solvable, hence contained
   in the zero radical. Therefore D has zero orthogonal complement. The
   double-orthogonal identity `lem-ag-bilinear-double-orthogonal` for symmetric
   nondegenerate forms in finite dimension gives D = (D orthogonal) orthogonal
   = the whole algebra. -/
theorem killingForm_nondegenerate_and_derived_eq_top_of_radical_eq_bot
    (k : Type u) (g : Type v) [Field k] [CharZero k]
    [LieRing g] [LieAlgebra k g] [FiniteDimensional k g]
    (hrad : radical k g = ⊥) :
    (killingForm k g).Nondegenerate ∧ derivedSeries k g 1 = ⊤ := by
  sorry

end LieAlgebra
