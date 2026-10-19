module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# The ring map on principal adic completions

Source: Temkin, Stable modification of relative curves, Theorem 3.5.5, Step 3,
pp. 22--23 (blueprint: def-trf-adic-ring-completion-map).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace AdicCompletion

/-- A ring map preserves powers of the corresponding principal ideals.
Source: Temkin, Theorem 3.5.5, Step 3
(blueprint: def-trf-adic-ring-completion-map).
Proof: extension of ideals commutes with powers; extension of `(π)` is `(f π)`.
Apply the extension/comap adjunction to their equality. -/
theorem principal_pow_le_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (π : R) (n : ℕ) :
    Ideal.span {π} ^ n ≤ (Ideal.span {f π} ^ n).comap f := by
  sorry

/-- The canonical map on the nth residue of a principal completion.
Source: Temkin, Theorem 3.5.5, Step 3
(blueprint: def-trf-adic-ring-completion-map). -/
noncomputable def principalResidueMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (π : R) (n : ℕ) :
    AdicCompletion (Ideal.span {π}) R →+* S ⧸ Ideal.span {f π} ^ n :=
  (Ideal.quotientMap _ f (principal_pow_le_comap f π n)).comp
    (evalₐ (Ideal.span {π}) n).toRingHom

/-- The residue maps commute with transition maps.
Source: Temkin, Theorem 3.5.5, Step 3
(blueprint: def-trf-adic-ring-completion-map).
Proof: choose a representative for the nth residue. Its reduction represents every
lower residue, by compatibility in the source completion. Both composites send that
representative to its image under `f` modulo the lower power, so they agree. -/
theorem principalResidueMap_compatible
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (π : R) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {f π}) h).comp (principalResidueMap f π n) =
      principalResidueMap f π m := by
  sorry

/-- The actual inverse-limit ring map, defined coordinate by coordinate.
Source: Temkin, Theorem 3.5.5, Step 3
(blueprint: def-trf-adic-ring-completion-map). -/
noncomputable def principalRingMap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (π : R) :
    AdicCompletion (Ideal.span {π}) R →+* AdicCompletion (Ideal.span {f π}) S :=
  liftRingHom (Ideal.span {f π}) (principalResidueMap f π)
    (principalResidueMap_compatible f π)

end AdicCompletion
