module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

import Sheaf.RingTheory.HopfAlgebra.FiniteDualHopfModule
import Sheaf.RingTheory.RelativeHopfModuleKernels
import Sheaf.RingTheory.CoidealCoinvariantProjection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # A Frobenius functional on a finite commutative Hopf algebra

Source: Siqi Clover Zheng, Frobenius Algebra Structure in Hopf Algebras and Cohomology
Ring with Poincare Duality (17 October 2020), Theorem 4.15 and proof of Theorem 4.8,
printed pp. 9-10. (blueprint: lem-sfb-finite-hopf-frobenius-form)

The conclusion uses the actual multiplication pairing: the image of `a` evaluates at `x`
as `λ (x * a)`. No choice of a vector-space isomorphism replaces this pairing.
-/

set_option autoImplicit false

@[expose] public section

universe u v w

namespace HopfAlgebra

/-- A finite-dimensional commutative Hopf algebra admits a linear functional whose
multiplication pairing identifies it bijectively with its algebraic linear dual.

Source: Zheng, Theorem 4.15 and proof of Theorem 4.8, printed pp. 9-10.
(blueprint: lem-sfb-finite-hopf-frobenius-form)

Proof plan from the accepted DAG split:
1. By lem-sfb-finite-dual-hopf-module, the dual has the action
   (h dot f)(x) = f(S(h) * x) and its evaluation-characterized compatible coaction.
   Apply lem-sfb-relative-hopf-module-kernels to A = k1 inside H. Its augmentation
   ideal is zero, so its quotient coalgebra is H. The retraction h maps to epsilon(h)1
   is A-linear and restricts to the identity on A. By lem-sfb-coideal-coinvariant-projection,
   tensoring the inclusion of coinvariants C with H is injective. Both parts of
   lem-sfb-relative-hopf-counit-criterion now give a bijection
   mu : H tensor_k C to H*, sending h tensor f to h dot f. The counit is nonzero,
   so H* is nonzero, and surjectivity of mu implies C is nonzero.
2. Choose a nonzero lambda in C and x0 with lambda(x0) nonzero. The functional
   t(f) = f(x0) / lambda(x0) on C takes lambda to 1. By the universal property in
   def-weil-pbc-module-tensor-product, h tensor f maps to t(f)h is a left inverse
   of h maps to h tensor lambda. Thus T(h)(x) = lambda(S(h) * x) is injective.
3. If S(h) is zero, T(h) is zero, so h is zero. Hence S is injective and therefore
   surjective by lem-sfb-finite-linear-injective-surjective in finite dimension.
4. Set Phi(a)(x) = lambda(x * a). If Phi(a) is zero, choose h with S(h) = a.
   Commutativity gives T(h) = Phi(a), so injectivity of T implies h = 0 and a = 0.
   Thus Phi is injective. The equality of the finite dimensions of H and H* from
   lem-sfb-linear-dual-dimension-rank and lem-sfb-finite-linear-injective-surjective
   make Phi surjective as well. -/
theorem exists_frobenius_functional (k : Type u) [Field k] (H : Type v) [CommRing H]
    [HopfAlgebra k H] (ι : Type w) [Finite ι] (basis : Module.Basis ι k H) :
    ∃ φ : Module.Dual k H,
      Function.Bijective (fun a : H => φ.comp ((LinearMap.mul k H).flip a)) := by
  sorry

end HopfAlgebra
