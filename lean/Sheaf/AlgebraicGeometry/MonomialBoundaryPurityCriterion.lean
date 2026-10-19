/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.PunctualPurity
public import Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.KrullDimension.Basic

import Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity
import Sheaf.AlgebraicGeometry.PunctualPurityTwoOfThree

/-!
# Coordinate-divisor criterion for monomial punctual purity

Source: ILO, Exposé XVI, Definitions 3.2.1--3.2.2 and Lemma 3.5.13(iv), printed pp.244,251
(blueprint: lem-per-monomial-boundary-purity-criterion).

All coefficients are the existing lifted prime-power coefficients at level one. The
supported class and punctual-purity predicate are the published constructions in D+.
This is the ordinary small-etale class, with its fixed positive Kummer normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The actual quotient cutting out the i-th coordinate divisor in the existing monomial
trait algebra. Source: ILO XVI 3.5.11--3.5.13
(blueprint: lem-per-monomial-boundary-purity-criterion). -/
abbrev monomialBoundaryAlgebra (R : Type u) [CommRing R]
    (π : R) (n : ℕ) (a : Fin n → ℕ) (i : Fin n) :=
  monomialTraitAlgebra R π n a ⧸
    Ideal.span ({Ideal.Quotient.mk (Ideal.span
      {(∏ j : Fin n, MvPolynomial.X j ^ a j) - MvPolynomial.C π})
      (MvPolynomial.X i)} : Set (monomialTraitAlgebra R π n a))

/-- The canonical closed coordinate-divisor inclusion, induced by the quotient map.
Source: ILO XVI Lemma 3.5.13(iv)
(blueprint: lem-per-monomial-boundary-purity-criterion). -/
abbrev monomialBoundaryInclusion (R : Type u) [CommRing R]
    (π : R) (n : ℕ) (a : Fin n → ℕ) (i : Fin n) :
    Spec (.of (monomialBoundaryAlgebra R π n a i)) ⟶
      Spec (.of (monomialTraitAlgebra R π n a)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

/-- The coordinate inclusion is the spectrum of the existing surjective quotient map.
This instance is a direct application of Mathlib's closed-immersion construction.
Source: ILO XVI Lemma 3.5.13(iv)
(blueprint: lem-per-monomial-boundary-purity-criterion). -/
instance monomialBoundaryInclusion_isClosedImmersion (R : Type u) [CommRing R]
    (π : R) (n : ℕ) (a : Fin n → ℕ) (i : Fin n) :
    IsClosedImmersion (monomialBoundaryInclusion R π n a i) :=
  AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk _)) Ideal.Quotient.mk_surjective

/-- Punctual purity of a regular monomial trait model is equivalent to purity of precisely
its positive-exponent coordinate divisors, with the fixed Kummer class.

Source: ILO XVI Lemma 3.5.13(iv), printed p.251
(blueprint: lem-per-monomial-boundary-purity-criterion).

Proof:
1. The finite-type monomial model and its generic open are Noetherian; regularity restricts
   to the open. Invertibility of ell is inherited from R. Use def-weil-finite-type-morphism,
   lem-weil-pbc-finite-type-over-noetherian, and
   lem-weil-pbc-noetherian-open-subscheme-noetherian.
2. For a positive exponent, setting T_i to zero gives the polynomial ring in the remaining
   variables over R/(pi). Thus H_i is regular Noetherian and is a codimension-one Cartier
   divisor. Use sbc-lem-affine-space-smooth and lem-per-regular-lci-geometric-calculus.
3. Each H_i and the generic open are regular schemes over a field, hence over its prime
   field. Apply lem-per-prime-field-punctual-purity. The generic open needs no smoothness
   over the original fraction field: R[1/pi] is a field by the trait hypotheses.
4. Primality and the monomial equation say that the positive-exponent H_i cover the special
   fibre set-theoretically. Together with the generic open these cover V.
5. If V is punctually pure, apply lem-per-punctual-purity-two-of-three to H_i in V, with
   punctual purity of H_i from step 3, obtaining purity of the supported Kummer map.
6. Conversely, purity of that map and of H_i gives punctual purity along H_i by the same
   two-of-three theorem. Step 3 handles the generic open and step 4 covers all points.
   The normalization in lem-per-regular-immersion-class-calculus identifies every map used.
   For n=1 the divisor is Spec(R/(pi)); exponent-zero variables remain free variables.
-/
theorem monomial_boundary_purity_criterion
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (π : R)
    (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π}) (hℓR : IsUnit (ℓ : R))
    (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℕ) (ha : ∃ i, a i ≠ 0)
    (hregular : IsRegularScheme (Spec (.of (monomialTraitAlgebra R π n a)))) :
    IsPunctuallyPure ℓ hℓ (Spec (.of (monomialTraitAlgebra R π n a))) ↔
      ∀ (i : Fin n), 0 < a i →
        ∃ (hreg : IsStalkRegularClosedImmersion (monomialBoundaryInclusion R π n a i) 1)
          (hunit : IsUnit ((ℓ ^ 1 : ℕ) :
            Γ(Spec (.of (monomialTraitAlgebra R π n a)), ⊤))),
          IsIso (punctualPurityClassMap ℓ hℓ
            (monomialBoundaryInclusion R π n a i) 1 hreg hunit) := by
  sorry

end AlgebraicGeometry.Etale
