/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q57
-/
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-!
# Domains and common fraction field for monoid algebras

Source: ILO, Exposé VIII, 3.2.4, Lemma 3.2.9 and the first proof paragraph of
Lemma 3.2.12, printed pp. 103–104 (blueprint: lem-trf-monoid-algebra-domain-fraction).
The additive monoid conventions are those of `def-trf-fine-fan-blowup`.
-/

set_option autoImplicit false

universe u v

namespace AddMonoidAlgebra

/-- The monomial inclusion of a generating affine submonoid of a torsion-free abelian group
is injective, both monoid algebras are domains, and their fraction fields are canonically
identified. The ring equivalence extends the specified monomial inclusion; the last clause
writes every group monomial as a quotient, in cross-multiplied form inside the group algebra.
Source: ILO, Exposé VIII, 3.2.4, Lemma 3.2.9 and Lemma 3.2.12, printed pp. 103–104
(blueprint: lem-trf-monoid-algebra-domain-fraction).

Proof plan:
1. The map sends each basis monomial to its image under the subtype inclusion. Reading its
   coefficients back on `Q` proves injectivity. The coefficient at zero of the identity is one.
2. The submonoid is cancellative and torsion-free. Its finite generation gives unique sums by
   `lem-trf-affine-monoid-unique-sums` (`AffineAddMonoid.to_twoUniqueSums`).
3. For two nonzero polynomials, select the uniquely represented sum of elements of their
   finite nonempty supports. Its product coefficient is a product of two nonzero field
   elements. Thus the submonoid algebra is a domain.
4. The set of differences `a - b` with `a, b ∈ Q` is a subgroup containing `Q`, hence all of `G`.
   Therefore each `g` is `a - b`, and its monomial times the monomial of `b` is that of `a`.
   Group monomials are units and in particular nonzero.
5. For a finite sum with exponents `g`, choose `g = a_g - b_g` and use the monomial of
   `b = ∑ g, b_g` to clear all exponents simultaneously. For empty support choose `b = 0`.
6. Clear denominators of two nonzero group-algebra elements by these units. A vanishing
   product would contradict the submonoid-algebra domain and the injectivity in step 1.
7. Extend the inclusion to fractions by keeping numerators and denominators. Equality of
   cross products and step 1 prove this map well defined and injective. For a fraction `F/H`,
   clear the supports to obtain `f = e^b F` and `h = e^d H` in the submonoid algebra. Then
   `F/H = (e^d f)/(e^b h)`, with nonzero denominator, proving surjectivity. The resulting
   equivalence extends the original inclusion, and step 4 gives the last clause. -/
theorem domain_fraction_of_fg_generating_submonoid
    (k : Type u) [Field k] (G : Type v) [AddCommGroup G] [IsAddTorsionFree G]
    (Q : AddSubmonoid G) (hfg : Q.FG)
    (hgen : AddSubgroup.closure (Q : Set G) = ⊤) :
    Function.Injective (mapDomainRingHom k Q.subtype) ∧
      IsDomain (AddMonoidAlgebra k Q) ∧
      IsDomain (AddMonoidAlgebra k G) ∧
      (∃ e : FractionRing (AddMonoidAlgebra k Q) ≃+*
          FractionRing (AddMonoidAlgebra k G),
        ∀ f : AddMonoidAlgebra k Q,
          e (algebraMap (AddMonoidAlgebra k Q) (FractionRing (AddMonoidAlgebra k Q)) f) =
            algebraMap (AddMonoidAlgebra k G) (FractionRing (AddMonoidAlgebra k G))
              (mapDomainRingHom k Q.subtype f)) ∧
      (∀ g : G, ∃ a b : Q,
        single g (1 : k) * single (b : G) (1 : k) = single (a : G) (1 : k)) := by
  sorry

end AddMonoidAlgebra
