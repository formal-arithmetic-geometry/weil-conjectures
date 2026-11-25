/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic

/-!
# Essentially smooth ring maps

## References

* Stacks Project, Smoothing Ring Maps, Section 07FF, where the term is used in Lemmas 07FH and
  07FI; modelled on Algebra, Definition 00QM
-/

@[expose] public section

universe u v

namespace Algebra

/-- A commutative `R`-algebra `D` is essentially smooth when it is isomorphic, as an
`R`-algebra, to the localization of a smooth `R`-algebra `P` at a multiplicative subset. -/
def EssentiallySmooth (R : Type u) (D : Type v) [CommRing R] [CommRing D] [Algebra R D] :
    Prop :=
  ∃ (P : Type (max u v)) (hP : CommRing P),
    letI : CommRing P := hP
    ∃ (hRP : Algebra R P),
      letI : Algebra R P := hRP
      Smooth R P ∧ ∃ (S : Submonoid P), Nonempty (D ≃ₐ[R] Localization S)

end Algebra
