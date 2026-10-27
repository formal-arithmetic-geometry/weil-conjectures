/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Sheaf.RingTheory.FactorizationLocallyNilpotent
import WeilConjectures.RingTheory.HenselianFactorizationCriterion

/-!
# Henselian projection kernels of a nil-kernel ring tower

Source: Stacks Project, More on Algebra, Tag 0CT7 (`lemma-limit-henselian`), for sequences
(blueprint: lem-sfb-nil-ring-tower-limit-henselian).

The index `n : ℕ` denotes the paper's positive index `n + 1`. The standard limit in
`CommRingCat` is the ring of compatible tuples, with componentwise ring operations.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- Every projection of a surjective ring sequence with elementwise nilpotent transition
kernels is surjective, identifies its target with the quotient by its kernel, and has a
henselian kernel contained in the Jacobson radical. Coprime monic factorizations lift
along the projection.

Source: Stacks Project, More on Algebra, Tag 0CT7 (`lemma-limit-henselian`)
(blueprint: lem-sfb-nil-ring-tower-limit-henselian).

Proof:
1. Fix a stage and an element there. Successively choose preimages at all later stages
   using transition surjectivity, and use transition composites at earlier stages.
   This compatible tuple proves projection surjectivity. The canonical kernel-quotient
   map is therefore bijective, giving the asserted quotient identification.
2. Every composite transition has nil kernel: if the image of an element is nilpotent
   at the penultimate stage, a power lies in the last kernel, and another power is zero.
   The exponents may depend on the element. If any stage is the zero ring, nilness of
   the next kernel forces that next stage to be zero; all stages and the limit are zero.
3. For an element congruent to one at the fixed stage, its coordinates are one plus
   nilpotents at all later stages. Geometric sums invert these coordinates; their
   inverses are compatible by uniqueness of inverses. Earlier coordinates are one.
   Thus one plus every kernel element is a unit. Apply the radical criterion
   `lem-weil-pbc-jacobson-radical-one-plus-units` to obtain the Jacobson inclusion.
4. Coprimality survives lifting across a nil-kernel transition: lift the finitely many
   coefficients of a Bezout identity. The error polynomial has nil coefficients and
   is nilpotent by `lem-weil-pbc-locally-nilpotent-extension`. One plus that error is
   a unit; multiplying the lifted identity by its inverse gives a Bezout identity.
5. Starting from the prescribed factorization, recursively lift monic factors using
   `lem-weil-pbc-henselian-factorization-locally-nilpotent` and the canonical
   identification of each target with the quotient by the transition kernel.
   Step 4 preserves coprimality at every step.
6. Outside the zero-ring case, monic degrees are preserved by these maps. Thus the
   factors have fixed finite degrees. Form each coefficient as a compatible tuple,
   extending it to earlier stages by the transitions. The resulting monic polynomials
   have the required reductions. Their product equals the original polynomial at
   every stage, hence coefficientwise in the limit. Degree-zero factors are included.
7. Apply `lem-weil-pbc-henselian-factorization-criterion` to the Jacobson inclusion
   and the factorization lifting property, transported along the canonical quotient
   identification, to obtain the recorded `HenselianRing` notion. -/
theorem limit_henselian_of_surjective_nil_ker
    (F : ℕᵒᵖ ⥤ CommRingCat.{u})
    (hsurj : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom)
    (hnil : ∀ (n : ℕ) (x : F.obj ⟨n + 1⟩),
      x ∈ RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom → IsNilpotent x) :
    ∀ n : ℕ,
      Function.Surjective (limit.π F ⟨n⟩).hom ∧
      Function.Bijective (RingHom.kerLift (limit.π F ⟨n⟩).hom) ∧
      RingHom.ker (limit.π F ⟨n⟩).hom ≤ Ideal.jacobson (⊥ : Ideal (limit F : CommRingCat.{u})) ∧
      HenselianRing (limit F : CommRingCat.{u}) (RingHom.ker (limit.π F ⟨n⟩).hom) ∧
      ∀ (f : Polynomial (limit F : CommRingCat.{u})), f.Monic →
        ∀ (gₙ hₙ : Polynomial (F.obj ⟨n⟩)), gₙ.Monic → hₙ.Monic →
          IsCoprime gₙ hₙ → f.map (limit.π F ⟨n⟩).hom = gₙ * hₙ →
          ∃ g h : Polynomial (limit F : CommRingCat.{u}),
            g.Monic ∧ h.Monic ∧ f = g * h ∧
              g.map (limit.π F ⟨n⟩).hom = gₙ ∧ h.map (limit.π F ⟨n⟩).hom = hₙ := by
  sorry

end CommRingCat
