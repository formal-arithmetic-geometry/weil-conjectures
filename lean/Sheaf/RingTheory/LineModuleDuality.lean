module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# Dual evaluation and scalar endomorphisms of a line module

Source: Stacks Project, `literature/stacks-project/more-algebra.tex`, Tag 0B8I
(lemma-invertible), evaluation proof, and Tag 0FJ9 (section-determinants), the
paragraph before remark-determinant-as-socle (blueprint: lem-trf-line-module-duality).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- The dual of a finite projective module whose prime localizations are isomorphic
 to the localized ring is its tensor inverse, and scalar multiplication identifies
 the ring with its module of endomorphisms.

Source: Stacks Project, More on Algebra, Tag 0B8I (lemma-invertible), equivalence
(1)--(3) and its evaluation proof; Tag 0FJ9 (section-determinants), the identification
`R = Hom_R(L,L)` before remark-determinant-as-socle
(blueprint: lem-trf-line-module-duality).

Proof:
1. The finite projective hypothesis is the direct-summand-of-finite-free hypothesis
of def-weil-pbc-projective-module. Choose a splitting i : L -> R^n, s : R^n -> L.
Put x_j = s(e_j), lambda_j = pr_j i. The identity s i = id gives
x = sum_j lambda_j(x) x_j, and applying a functional gives
lambda = sum_j lambda(x_j) lambda_j. This includes n = 0.
2. Extend lambda to each prime localization by lambda_p(x/a) = lambda(x)/a,
using def-weil-pbc-module-localization. The fraction relation is preserved because
u(bx - ay) = 0 implies u(b lambda(x) - a lambda(y)) = 0. In a chosen rank-one
local basis, lambda(x)y - lambda(y)x has zero localization. Applying each lambda_j
and lem-weil-pbc-prime-localizations-jointly-injective makes every coordinate zero;
the dual-basis expansion gives lambda(x)y = lambda(y)x globally.
3. Set t = sum_j lambda_j(x_j). At a prime, write x_j/1 = a_j v and
b_j = (lambda_j)_p(v), for a free generator v. The localized dual-basis expansion
at v gives sum_j b_j a_j = 1. Thus t/1 = 1 at every prime; the same joint
injectivity gives t = 1. For the zero ring, this is the empty-prime case of that
injectivity assertion.
4. The evaluation is contractLeft, by def-weil-pbc-module-tensor-product and its
universal property. Set xi = sum_j lambda_j tensor x_j. The map a(r) = r xi
satisfies e a(r) = r by step 3. On lambda tensor x, balancing and step 2 give
a e(lambda tensor x) = sum_j lambda_j tensor lambda(x) x_j
= sum_j lambda_j tensor lambda(x_j) x
= (sum_j lambda(x_j) lambda_j) tensor x = lambda tensor x.
Pure tensors generate, so a e = id. Tensor symmetry then gives the bijectivity of
contractRight as well, expressing that the dual is a tensor inverse in both orders.
5. For f : L -> L put h(f) = sum_j lambda_j(f(x_j)). This is R-linear.
Steps 1 and 2 give f(x) = sum_j lambda_j(x) f(x_j) = h(f) x, so c h = id.
Step 3 gives h(c(r)) = r sum_j lambda_j(x_j) = r. Thus the R-linear scalar map
c = LinearMap.lsmul R L is bijective, with inverse h. -/
theorem line_module_duality
    (R : Type u) [CommRing R] (L : Type v) [AddCommGroup L] [Module R L]
    [Module.Finite R L] [Module.Projective R L]
    (hlocal : ∀ (p : Ideal R) [p.IsPrime],
      Nonempty (LocalizedModule p.primeCompl L ≃ₗ[Localization.AtPrime p]
        Localization.AtPrime p)) :
    Function.Bijective (contractLeft R L) ∧
      Function.Bijective (LinearMap.lsmul R L) ∧
      Function.Bijective (contractRight R L) := by
  sorry

end Module
