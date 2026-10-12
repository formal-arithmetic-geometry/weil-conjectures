/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.LiftMonicCoprimeFactorizationEtale

/-!
# Lifting a coprime factorization after an étale extension

Source: Stacks Project, More on Algebra, Tag 07M1, lemma-lift-factorization-easy
(blueprint: lem-weil-pbc-lift-coprime-factorization-etale).
-/

@[expose] public section

universe u

namespace Polynomial

/-- A coprime factorization modulo an arbitrary ideal, whose first factor has unit leading
coefficient, lifts after an étale extension inducing an isomorphism on the quotient.
Source: Stacks Project, Tag 07M1, lemma-lift-factorization-easy
(blueprint: lem-weil-pbc-lift-coprime-factorization-etale).

Proof:
1. Choose a lift `a` of the leading coefficient of `g₀` and localize at `a`. By
   `lem-weil-pbc-lift-invertible-element` (Tag 07LX), this extension is étale, induces
   an isomorphism modulo `I`, and makes `a` a unit `u`.
2. Transport the factors along that quotient isomorphism and replace them by
   `u⁻¹ * g₀` and `u * h₀`. Their product and coprimality are preserved. The first
   factor is monic; since the product is monic the second is monic too. In the zero
   quotient ring every polynomial is monic, so this case is included.
3. Apply `lem-weil-pbc-lift-monic-coprime-factorization-etale` (Tag 0ALH) to obtain
   monic lifted factors after a further étale extension trivial on the quotient.
4. Compose the two étale extensions using `lem-weil-pbc-etale-composition-cancellation`.
   The induced quotient map is the composite of the quotient isomorphisms. If `v` is
   the image of `u` in the final ring, multiply the first lifted factor by `v` and
   the second by `v⁻¹`. Their product remains the image of `f`, and their reductions
   are precisely the transported original factors.
-/
theorem exists_etale_lift_coprime_factorization
    {A : Type u} [CommRing A] (I : Ideal A) (f : A[X]) (hf : f.Monic)
    (g₀ h₀ : (A ⧸ I)[X])
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀)
    (hleading : IsUnit g₀.leadingCoeff) (hcoprime : IsCoprime g₀ h₀) :
    ∃ (A' : Type u) (_ : CommRing A') (φ : A →+* A'),
      let J : Ideal A' := I.map φ
      let α : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧
        Function.Bijective α ∧
        ∃ g' h' : A'[X], f.map φ = g' * h' ∧
          g'.map (Ideal.Quotient.mk J) = g₀.map α ∧
          h'.map (Ideal.Quotient.mk J) = h₀.map α := by
  sorry

end Polynomial
