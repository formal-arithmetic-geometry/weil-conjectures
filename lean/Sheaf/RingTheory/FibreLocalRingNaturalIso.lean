/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# The natural local-ring map of a fibre

Source: Stacks Project, Algebra, Remarks 0H9M and 00E6
(blueprint: lem-weil-pbc-fibre-ring-local-ring-natural-iso).
-/

universe u v

namespace Ideal

/-- The canonical map from `B_q` to the local ring of the fibre at `Q` is surjective,
with kernel `p B_q`, and induces the quotient isomorphism with its natural fraction formula.
Source: Stacks Project, Algebra, Remarks 0H9M and 00E6
(blueprint: lem-weil-pbc-fibre-ring-local-ring-natural-iso).

Proof:
1. Set `D = (A \ p)⁻¹ B` and `I = p D`. The canonical `B`-algebra isomorphism
   `p.Fiber B ≃ D/I` sends `j(b)` to the class of `b/1`
   (lem-weil-pbc-fibre-ring-localization-quotient). Pull `Q` back to a prime `r` of `D`.
   Its contraction to `B` is `q`. Elements outside `p` become units in `D`, and elements
   of `p` vanish in `D/I`, so the contraction of `q` to `A` is `p`.
2. The natural isomorphism `B_q ≃ D_r` sends `b/s` to `i(b)/i(s)`
   (lem-weil-pbc-localization-prime-residue-field-iso). It sends `p B_q` onto `I D_r`,
   since both ideals have the same displayed generators. The map `D_r → (D/I)_Q`
   is surjective with kernel `I D_r` (lem-weil-pbc-localization-at-prime-of-quotient).
   Transporting along the fibre isomorphism gives exactly the canonical local-ring map,
   with the asserted fraction formula, surjectivity, and kernel.
3. Apply the first isomorphism theorem. Its quotient isomorphism sends the class of each
   element `x` to its image under the canonical map, hence sends `[b/s]` to `j(b)/j(s)`.

Mathlib uses `κ(p) ⊗[A] B` for the fibre; tensor symmetry identifies `j(b) = 1 ⊗ b`
with the source's `b ⊗ 1`. The algebra structure encodes the arbitrary ring map `A → B`. -/
theorem Fiber.localRingHom_surjective_ker_quotientEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (Q : Ideal (p.Fiber B)) [Q.IsPrime] :
    let j : B →+* p.Fiber B := Algebra.TensorProduct.includeRight.toRingHom
    let q : Ideal B := Q.comap j
    let θ := Localization.localRingHom q Q j rfl
    let I : Ideal (Localization.AtPrime q) :=
      (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q))
    (∀ (b : B) (s : q.primeCompl),
      θ (Localization.mk b s) = Localization.mk (j b) ⟨j s, s.property⟩) ∧
    Function.Surjective θ ∧ RingHom.ker θ = I ∧
    ∃ e : (Localization.AtPrime q ⧸ I) ≃+* Localization.AtPrime Q,
      ∀ x : Localization.AtPrime q, e (Ideal.Quotient.mk I x) = θ x := by
  sorry

end Ideal
