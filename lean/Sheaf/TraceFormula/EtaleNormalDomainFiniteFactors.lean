module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Algebra.Pi
import Sheaf.RingTheory.EtaleNormalRing
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions

/-!
# Finite normal-domain factors of an étale algebra over a normal domain

Source: literature/stacks-project/algebra.tex, Tag 030C (lemma-characterize-reduced-ring-normal),
implication (1) to (3), applied to an étale algebra over a domain; the finite generic-fibre
argument uses Tags 00FN, 00FR, 00HS and 00E3.
(blueprint: lem-trf-etale-normal-domain-finite-factors)
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry

/--
If `A` is a normal integral domain and `B` is an étale `A`-algebra, then `B` is a finite
product of normal integral domains as an `A`-algebra.  The proof follows the source's
combination of Stacks Tag 030C with the generic-fibre and prime-localization arguments:

1. If `B` is zero, choose the empty product.  Otherwise, étale ascent of normality and
   detection by prime localizations show that `B` is reduced and normal.
2. Étaleness gives local finite presentation, and the affine finite-presentation criterion
   makes `B` a finitely presented, hence finitely generated, `A`-algebra.
3. Localize at the nonzero elements of `A`.  The resulting algebra over `Frac A` is finite type,
   so it is Noetherian and has finitely many minimal primes.
4. Flat going-down puts every minimal prime of `B` over `(0)` in `A`; prime localization
   correspondence injects the minimal primes of `B` into those of the generic fibre.
5. The reduced-normal finite-minimal-prime criterion (Tag 030C, (1) to (3)) gives a finite
   product of normal integral domains.  Transporting the `A`-algebra structure along the ring
   isomorphism makes it an `A`-algebra isomorphism.  This also covers the empty product and
   imposes no Noetherian hypothesis on either ring.

Source: literature/stacks-project/algebra.tex, Tag 030C (lemma-characterize-reduced-ring-normal),
implication (1) to (3), with the generic-fibre and prime-localization steps from Tags 00FN,
00FR, 00HS and 00E3. (blueprint: lem-trf-etale-normal-domain-finite-factors)
-/
theorem etale_normal_domain_finite_factors
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hA : IsDomain A ∧ IsIntegrallyClosed A)
    (hEtale : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    ∃ (n : ℕ) (B₁ : Fin n → Type u) (_ : ∀ j, CommRing (B₁ j))
      (_ : ∀ j, Algebra A (B₁ j)),
      ∃ (_ : ∀ j, IsDomain (B₁ j) ∧ IsIntegrallyClosed (B₁ j)),
        Nonempty (B ≃ₐ[A] (∀ j, B₁ j)) := by
  sorry

end AlgebraicGeometry
