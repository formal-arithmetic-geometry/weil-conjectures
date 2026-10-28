/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.CohomologicalDimension
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Degree two with prime coefficients over a finite field

Source: the finite cyclic quotient argument in `sk-lem-base-field-cd-finite-field`.
(blueprint: lem-sfb-finite-field-prime-degree-two)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace DiscreteModule

/-- The degree-two continuous cohomology of a finite field with trivial prime
coefficients prime to the characteristic vanishes.

Source: blueprint `sk-lem-base-field-cd-finite-field.proof.md`, paragraphs
Finite modules and Consequences; `det-base-field-cd-cochains`, clause (3), and
`det-base-field-cd-inflation`, final clause.
(blueprint: lem-sfb-finite-field-prime-degree-two)

Proof: The absolute Galois group of K is the profinite completion of the integers,
with Frobenius corresponding to one. Continuous cochains with the finite trivial
coefficient group Z/ℓ factor through finite cyclic quotients. Their second cohomology
is therefore the filtered colimit of the second cohomology of these quotients along
inflation. A representative at the cyclic quotient of order n becomes zero at the
quotient of order ℓ*n: cyclic inflation in degree two multiplies by ℓ in the periodic
resolution and the coefficient group is killed by ℓ. Every element of the colimit
vanishes. The equivalence of continuous cochain cohomology with Ext from the trivial
integer module gives the stated vanishing. This includes the quotient of order one
and requires no roots of unity in K. The characteristic-primary case is handled
separately by Artin–Schreier in the importing module. -/
theorem subsingleton_H_two_trivialZMod_of_finiteField
    (K Ks : Type u) [Field K] [Finite K] [Field Ks] [Algebra K Ks]
    [IsSepClosure K Ks] (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : (ℓ : K) ≠ 0) :
    Subsingleton (H Gal(Ks/K) (trivialZMod.{u + 1} Gal(Ks/K) ℓ) 2) := by
  sorry

end DiscreteModule
