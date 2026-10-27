module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
import Sheaf.AlgebraicGeometry.SemisimpleCharactersTrivial
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # Complete reducibility in characteristic zero

Source: Milne, Algebraic Groups (2017), Section 22c, Proposition 22.41, p.477;
characteristic zero is the standing hypothesis on p.475.
(blueprint: lem-sfb-characteristic-zero-complete-reducibility)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.RationalHighestWeight

/-- Every finite-dimensional rational module for a semisimple group in characteristic
zero is an internal finite direct sum of simple rational submodules. The coaction on
each summand is specified by its intertwining inclusion, so the summands are submodules
of the given coaction. The index `Fin n` includes the empty decomposition when `V = 0`.

Source: Milne, Algebraic Groups (2017), Section 22c, Proposition 22.41, p.477.
(blueprint: lem-sfb-characteristic-zero-complete-reducibility)

Proof:
1. Characters of G are trivial by lem-sfb-semisimple-characters-trivial. By
   lem-sfb-simple-hyperplane-splitting-criterion (Milne 22.40), it suffices to split
   every simple codimension-one rational submodule W of every rational module U.
2. If the action on U is trivial, any vector-space line complement is rational.
   Otherwise lem-sfb-semisimple-group-casimir-trace gives an equivariant endomorphism
   c with trace n, for a positive integer n. It preserves W. The one-dimensional
   quotient U/W is a character, hence trivial, and the Casimir lemma gives c(U) <= W.
3. By lem-zl-alg-closed-endomorphism-eigenvalue, c restricted to nonzero W has an
   eigenvalue a. Its nonzero eigenspace is rational: the coaction commutes with c-a
   and tensoring over a field preserves kernels. Simplicity makes this eigenspace W.
   In a basis extending one of W, the trace identity is a * dim(W) = n. Characteristic
   zero makes n nonzero, so a is nonzero.
4. The equivariant map a inverse times c, regarded as U to W, restricts to the
   identity on W. Its rational kernel L satisfies U = W + L and W intersection L = 0.
   The splitting criterion gives a finite simple decomposition. Restrict the original
   coaction to each summand; tensor injectivity gives its counit and coassociativity
   laws and its intertwining inclusion. Independence and spanning express the internal
   direct sum. For the zero module take n = 0.
-/
theorem characteristicZero_completeReducibility
    {F : Type u} [Field F] [IsAlgClosed F] [CharZero F]
    (G : Grp (Over (Spec (.of F)))) [IsAffine G.X.left]
    (hG : IsSemisimpleGroupScheme G.X)
    {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (c : V →ₗ[F] V ⊗[F] coordinateAlgebra G)
    (hcoassoc : HopfAction.Coassociative F (coordinateAlgebra G) V c)
    (hcounit : HopfAction.Counital F (coordinateAlgebra G) V c) :
    ∃ (n : ℕ) (N : Fin n → Submodule F V)
      (d : ∀ i : Fin n, N i →ₗ[F] (N i) ⊗[F] coordinateAlgebra G),
      iSupIndep N ∧ (⨆ i, N i) = ⊤ ∧
      ∀ i : Fin n,
        HopfAction.Coassociative F (coordinateAlgebra G) (N i) (d i) ∧
        HopfAction.Counital F (coordinateAlgebra G) (N i) (d i) ∧
        IsSimple (d i) ∧
        (N i).subtype.rTensor (coordinateAlgebra G) ∘ₗ d i = c ∘ₗ (N i).subtype := by
  sorry

end AlgebraicGeometry.RationalHighestWeight
