module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Localization.Defs
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal

/-!
# Flat base change of an integral intermediate total-fraction algebra

Source: Stacks Project, Algebra, Tags 00HB, 00CP, 00CX, 02JK and 034M; affine
algebra underlying ILO VIII, Lemma 2.2.9, printed p.91. The arbitrary integral
intermediate-algebra version is an agent generalization
(blueprint: lem-per-flat-integral-total-fractions).

`FractionRing D` is the localization at `nonZeroDivisors D`, including for rings
with zero divisors and the zero ring. This is the ring specialization of
`LocalizedModule (nonZeroDivisors D) D`, not a domain-only fraction field.
The fraction map is Mathlib's localization map; the tensor map and fraction
isomorphism are characterized by their values on generators.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

/-- Flat scalar extension of an arbitrary integral intermediate total-fraction algebra.

Source: Stacks Project, Algebra, Tags 00HB, 00CP, 00CX, 02JK and 034M; the affine
algebra underlying ILO VIII, Lemma 2.2.9, printed p.91, generalized to arbitrary
integral intermediate algebras (blueprint: lem-per-flat-integral-total-fractions).

Proof:
1. The total-fraction localization map is injective: a regular denominator cannot
   annihilate a nonzero element (`def-weil-pbc-module-localization`). For regular
   `s` in `A`, multiplication by `s` is injective on `A` and on `B`, where it is
   multiplication by a unit in `FractionRing A`. Flat tensoring with `R`
   (`lem-trf-flat-tensor-preserves-injection`) makes multiplication by its image
   injective on `R` and on `R ⊗[A] B`. Thus regular elements map to regular
   elements, defining the canonical fraction map by
   `lem-weil-pbc-ring-localization-universal-property`.
2. The tensor pushout (`lem-weil-pbc-algebra-tensor-pushout-universal-property`)
   constructs `j` with the displayed pure-tensor formula. Its composite with
   `R → R ⊗[A] B` is the injective localization map, so the structure map is
   injective.
3. Express a tensor element as a finite sum of pure tensors
   (`def-weil-pbc-module-tensor-product`). Choose one denominator per element of
   `B` appearing in this sum and multiply them, with empty product 1. Balancing
   gives `f(s)c = i(r)` for some `r` in `R`. If `j(c) = 0`, then `r/1 = 0`,
   so `r = 0`; injectivity of multiplication by `f(s)` from Step 1 gives `c = 0`.
4. Integral base change (`lem-weil-pbc-integral-base-change`) makes
   `R → R ⊗[A] B` integral, without a finiteness assumption.
5. Regard `R ⊆ C ⊆ FractionRing R` using these embeddings. Regular elements of
   `R` stay regular on `C`. For regular `t` in `C`, write `j(t) = r/u` with
   regular `u` in `R`. The relation `ut = r` and injectivity show `r` is regular
   in `R`. Hence `j(t)` is a unit with inverse `u/r`.
6. Localization's universal property extends `j` to `J : Q(C) → Q(R)` and the
   structure map to `H : Q(R) → Q(C)`. Their composite on `R` is the identity.
   For `c` in `C`, write `j(c) = r/u`; the relation `uc = i(r)` implies
   `HJ(c/1) = c/1`. Localization uniqueness gives both inverse identities.
7. Integrality puts the image of `j` in the integral closure of `R`. Conversely,
   transfer an integral equation for `x` along `H`; it makes `H(x)` integral
   over `C`. Under the displayed prime-local normality condition,
   `lem-weil-pbc-normal-ring-integrally-closed-total` puts `H(x)` in `C`.
   Applying `J` gives `x` in the image of `j`. These arguments also apply to the
   zero ring and use neither Noetherianity nor module finiteness.
-/
theorem flat_integral_totalFractions
    (A : Type u) (R : Type v) [CommRing A] [CommRing R]
    [IsReduced A] [IsReduced R] [Algebra A R]
    (hf : (algebraMap A R).Flat)
    (B : Subalgebra A (FractionRing A)) [Algebra.IsIntegral A B] :
    ∃ hregular : nonZeroDivisors A ≤ (nonZeroDivisors R).comap (algebraMap A R),
      ∃ j : R ⊗[A] B →ₐ[R] FractionRing R,
        (∀ (r : R) (b : B), j (r ⊗ₜ[A] b) = algebraMap R (FractionRing R) r *
          IsLocalization.map (FractionRing R) (algebraMap A R) hregular
            (b : FractionRing A)) ∧
        Function.Injective j ∧
        Function.Injective (algebraMap R (R ⊗[A] B)) ∧
        Algebra.IsIntegral R (R ⊗[A] B) ∧
        (∃ e : FractionRing (R ⊗[A] B) ≃+* FractionRing R,
          ∀ c : R ⊗[A] B, e (algebraMap (R ⊗[A] B) (FractionRing (R ⊗[A] B)) c) = j c) ∧
        ((∀ (p : Ideal (R ⊗[A] B)) [p.IsPrime],
          IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) →
          j.range = integralClosure R (FractionRing R)) := by
  sorry
