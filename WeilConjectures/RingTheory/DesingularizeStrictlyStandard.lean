/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.StrictlyStandardElement
public import WeilConjectures.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.DesingularizeAnnihilatorConstruction
import WeilConjectures.RingTheory.SingularIdealsOfAnnihilatorBound

/-!
# Desingularization along a strictly standard element

## Implementation details

Compatibility modulo the fourth power is stated on representatives; since every quotient class
has a representative, this is exactly the commuting triangle. The proof base changes to
`A ⊗[R] D` (with `D` Noetherian), where the element remains strictly standard, and applies
desingularization over `D` to obtain `B` with `aB ≤ H_{B/D}`, where `a` annihilates
`Ann_D(π²)/Ann_D(π)`. At `R`-flat primes of `D` this quotient vanishes, so `a` lies in no
smooth prime; the radical criterion then gives `H_{D/R}B ≤ H_{B/D}` and, by smooth base change
and composition, the inclusion into `H_{B/R}`.

## References

* [Stacks, Tag 07CT]
-/

@[expose] public section

universe u v w z

namespace Algebra

/-- Desingularization along a strictly standard element. Compatibility modulo the fourth
power is tested on representatives: if the image of `a` under the quotient map is represented
by `d`, their images in the quotient of `Λ` agree. -/
theorem exists_desingularization_strictlyStandard
    (R : Type u) (Λ : Type v) (A : Type w) (D : Type z)
    [CommRing R] [CommRing Λ] [CommRing A] [CommRing D]
    [Algebra R Λ] [Algebra R A] [Algebra R D] [IsNoetherianRing R]
    [FinitePresentation R A] [FinitePresentation R D]
    (π : R) (α : A →ₐ[R] Λ) (δ : D →ₐ[R] Λ)
    (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0)
    (hΛ : ∀ l : Λ, l * algebraMap R Λ π = 0 ↔
      l * (algebraMap R Λ π) ^ 2 = 0)
    (hstandard : IsStrictlyStandardElement (R := R) (algebraMap R A π))
    (hquot : ∃ φ :
      (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (D ⧸ Ideal.span {(algebraMap R D π) ^ 4}),
      ∀ (a : A) (d : D),
        φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ d →
        Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (δ d)) :
    ∃ (B : Type (max u v w z)) (_ : CommRing B) (_ : Algebra R B),
      FinitePresentation R B ∧
      ∃ (β : B →ₐ[R] Λ) (aB : A →ₐ[R] B) (dB : D →ₐ[R] B),
        β.comp aB = α ∧ β.comp dB = δ ∧
        Ideal.map dB.toRingHom (singularIdeal R D) ≤
          @singularIdeal D B _ _ dB.toRingHom.toAlgebra ∧
        Ideal.map dB.toRingHom (singularIdeal R D) ≤ singularIdeal R B := by
  obtain ⟨B, instB, instRB, β, aB, dB, hfp, ha, hd, hbound⟩ :=
    exists_desingularization_annihilator_bound R Λ A D π α δ hΛ hstandard hquot
  let : CommRing B := instB
  let : Algebra R B := instRB
  let : Algebra D B := dB.toRingHom.toAlgebra
  have : IsScalarTower R D B := IsScalarTower.of_algHom dB
  have : FinitePresentation D B := hfp
  have : FinitePresentation R B := FinitePresentation.trans R D B
  obtain ⟨hrelative, habsolute⟩ :=
    singularIdeals_of_annihilator_bound R D B dB hfp π hR hbound
  exact ⟨B, instB, instRB, inferInstance, β, aB, dB, ha, hd, hrelative, habsolute⟩

end Algebra
