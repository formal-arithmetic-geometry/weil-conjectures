module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.RingTheory.IndEtaleStability
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.TotalFractionFiberDecomposition
import Sheaf.RingTheory.WeaklyEtaleField
import Mathlib.RingTheory.Etale.Field

/-! # Total fractions under Noetherian ind-étale base change

Source: Stacks Project, Tag 0EN6, proof of `lemma-meromorphic-quasi-coherent`,
(1)-(2), extended from étale to ind-étale maps using Tags 092Q, 0CKR and 00U3
(blueprint: lem-per-ind-etale-total-fraction-comparison).

`FractionRing R` is the localization at all nonzerodivisors, including for
rings with zero divisors and the zero ring. It is the ring specialization of
`LocalizedModule (nonZeroDivisors R) R`. The tensor product uses Mathlib's
multiplication of pure tensors and its right-factor `B`-algebra structure.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Algebra

/-- The canonical total-fraction comparison for reduced Noetherian ind-étale algebras.
The algebra isomorphism is specified on every fraction tensored with an element of `B`;
these generators determine the map uniquely. Its `B`-algebra structure is the right-factor
structure, so its structure map sends `b` to `1 ⊗ b`.

Source: Stacks Project, Tag 0EN6, proof of `lemma-meromorphic-quasi-coherent`, (1)-(2),
with the ind-étale extension assembled from Tags 092Q, 0CKR and 00U3
(blueprint: lem-per-ind-etale-total-fraction-comparison).

Proof:
1. `lem-weil-pbc-ind-etale-stability` makes the map weakly étale and hence flat
   (`def-weil-pbc-ind-etale-algebra`). Tensor the injective multiplication by a
   nonzerodivisor of `A` with `B`, using `def-weil-pbc-flat-ring-map`.
   The identifications `A ⊗ B = B` from `def-weil-pbc-module-tensor-product`
   show that its image is a nonzerodivisor of `B`.
2. `lem-weil-pbc-localization-base-change` and tensor symmetry identify
   `Q(A) ⊗ B` with the localization `C` of `B` at the images of regular elements
   of `A`. By `lem-weil-pbc-total-fraction-fiber-decomposition`, `C` is the
   finite product of the fibres `κ(p) ⊗ B` at the minimal primes of `A`.
3. Each fibre is ind-étale, hence weakly étale, by
   `lem-weil-pbc-ind-etale-stability`. The singly generated subalgebra of any
   element is finite étale by `lem-weil-pbc-weak-etale-field`, and a finite
   product of fields by `lem-weil-pbc-etale-algebra-over-field-product`.
   Invert its nonzero coordinates and set the other coordinates to zero.
   Thus each element `x` of the fibre, and hence of `C`, satisfies `x = x²y`.
4. For a nonzerodivisor `t` of `B`, its image `x` in `C` remains regular:
   the localization zero criterion (`def-weil-pbc-module-localization`)
   reduces cancellation to cancellation of `t` in `B`. Now `x = x²y`
   implies `x(1-xy) = 0`, hence `xy = 1`. Thus every regular `t` becomes a unit.
5. Fraction formulas define `C → Q(B)`. A fraction in its kernel has numerator
   annihilated by a regular element of `B`, hence zero. Every fraction `b/t`
   is in the image by step 4. Compose this bijection with step 2 to obtain
   the asserted algebra isomorphism and formula. Empty products and zero rings
   are allowed throughout; no nontriviality or injectivity of `A → B` is used.
-/
theorem indEtale_totalFraction_comparison
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsReduced A] [IsReduced B]
    (hind : RingHom.IndEtaleAcrossUniverses (algebraMap A B)) :
    ∃ hregular : nonZeroDivisors A ≤ (nonZeroDivisors B).comap (algebraMap A B),
      ∃ e : @AlgEquiv B (FractionRing A ⊗[A] B) (FractionRing B) _ _ _
        Algebra.TensorProduct.rightAlgebra _,
        ∀ (a : A) (s : nonZeroDivisors A) (b : B),
          e (IsLocalization.mk' (FractionRing A) a s ⊗ₜ[A] b) =
            IsLocalization.mk' (FractionRing B) (algebraMap A B a * b)
              (⟨algebraMap A B s, hregular s.property⟩ : nonZeroDivisors B) := by
  sorry

end Algebra
