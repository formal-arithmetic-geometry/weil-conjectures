module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Finite type lifts along a nilpotent ideal

Source: More on Morphisms, Lemma 09ZW, proof, “The translation of (2) into algebra”
(blueprint: lem-weil-pbc-finite-type-lift-nilpotent)
-/

@[expose] public section

open scoped Polynomial

/-- If a quotient by a nilpotent ideal is of finite type, then the original ring map
is of finite type.  This is the ring translation of More on Morphisms, Lemma 09ZW.
The proof lifts generators and applies Nakayama's lemma for a nilpotent ideal.
(blueprint: lem-weil-pbc-finite-type-lift-nilpotent) -/
theorem finiteType_of_quotient_finiteType_nilpotent
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (hI : ∃ n : ℕ, I ^ (n + 1) = ⊥)
    (hquot : RingHom.FiniteType
      (Ideal.quotientMap (I.map φ) φ (Ideal.le_comap_map))) :
    RingHom.FiniteType φ := by
  sorry
