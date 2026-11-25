/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Idempotents
import WeilConjectures.RingTheory.QuotientHenselianPair
import WeilConjectures.RingTheory.HenselianIntegralIdempotentLifting

/-!
# Quotients of strictly henselian local rings

The quotient of a strictly henselian local ring by an ideal contained in its maximal ideal is a
strictly henselian local ring with the same residue field
(`isStrictlyHenselianLocalRing_quotient`).

## Implementation details

Any finite `A/I`-algebra is finite over `A`, and extending `m/I` to it is the same as extending
`m`, so the idempotent-lifting criterion for henselianity transfers from `A` to `A/I`.

## References

* [Stacks, Tag 05WS]
* [Stacks, Tag 04GF]
* [Stacks, Tag 09XI]
-/

@[expose] public section

universe u v

/-- A quotient by an ideal contained in the maximal ideal of a strictly henselian local
ring is local with the image maximal ideal and the same residue field, and is strictly
henselian, with unique idempotent lifting in every finite algebra. -/
theorem isStrictlyHenselianLocalRing_quotient
    (A : Type u) [CommRing A] [IsLocalRing A]
    (hA : IsStrictlyHenselianLocalRing A) (I : Ideal A)
    (hI : I ≤ IsLocalRing.maximalIdeal A) :
    ∃ (_ : IsLocalRing (A ⧸ I)),
      IsLocalRing.maximalIdeal (A ⧸ I) =
        (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) ∧
      (∃ e : IsLocalRing.ResidueField (A ⧸ I) ≃+* IsLocalRing.ResidueField A,
        ∀ a : A, e (IsLocalRing.residue (A ⧸ I) (Ideal.Quotient.mk I a)) =
          IsLocalRing.residue A a) ∧
      IsStrictlyHenselianLocalRing (A ⧸ I) ∧
      IsSepClosed (IsLocalRing.ResidueField A) ∧
      ∀ (B : Type (max u v)) [CommRing B] [Algebra (A ⧸ I) B] [Module.Finite (A ⧸ I) B],
        ∀ e : B ⧸ (IsLocalRing.maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) B),
          IsIdempotentElem e →
            ∃! b : B, IsIdempotentElem b ∧
              Ideal.Quotient.mk
                ((IsLocalRing.maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) B)) b = e := by
  classical
  let : IsStrictlyHenselianLocalRing A := hA
  have hproper : I ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hI
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let f := IsLocalRing.ResidueField.map (Ideal.Quotient.mk I)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨IsLocalRing.residue A a, rfl⟩
  let e := RingEquiv.ofBijective f ⟨f.injective, hsurj⟩
  have hres : ∀ a : A,
      e.symm (IsLocalRing.residue (A ⧸ I) (Ideal.Quotient.mk I a)) =
        IsLocalRing.residue A a := by
    intro a
    exact e.symm_apply_apply (IsLocalRing.residue A a)
  have hpair := IsLocalRing.henselianRing_quotient_maximalIdeal A I hI
  rw [hmax] at hpair
  let : HenselianRing (A ⧸ I) (IsLocalRing.maximalIdeal (A ⧸ I)) := hpair
  let : HenselianLocalRing (A ⧸ I) := {
    is_henselian := fun f hf a ha hu ↦
      HenselianRing.is_henselian f hf a ha (hu.map _) }
  let : IsSepClosed (IsLocalRing.ResidueField (A ⧸ I)) :=
    IsSepClosed.of_ringEquiv e
  have hstrict : IsStrictlyHenselianLocalRing (A ⧸ I) := ⟨inferInstance⟩
  refine ⟨inferInstance, hmax.symm, ⟨e.symm, hres⟩, hstrict, inferInstance, ?_⟩
  intro B _ _ _ b hb
  exact Algebra.existsUnique_isIdempotentElem_of_henselianRing
    (A ⧸ I) (IsLocalRing.maximalIdeal (A ⧸ I)) B b hb
