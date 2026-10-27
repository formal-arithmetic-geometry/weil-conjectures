/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.KoszulRegularFlatBaseChange
import WeilConjectures.RingTheory.KoszulConormalBasis

/-!
# Koszul generators from a conormal fibre basis

Source: Stacks Project, Divisors, Tag 067N (lemma-generate-regular-ideal), assertion (3),
applied to the ideal sheaf associated to an ideal on an affine scheme.
(blueprint: lem-sfb-koszul-generators-from-fibre-basis)

The fibre `p.ResidueField ⊗[A] I` is the canonical tensor presentation of
`I_p / p I_p`. Indeed localization identifies `A_p ⊗[A] I` with the extended
ideal `I_p`, and tensoring with the residue field quotients by its maximal ideal.
Under this identification `1 ⊗ f i` is precisely the class of the localized generator.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Ideal

/-- Lifts of a basis of the conormal fibre give Koszul-regular generators on a
principal neighbourhood of the prime.

Source: Stacks Project, Divisors, Tag 067N (lemma-generate-regular-ideal), assertion (3).
(blueprint: lem-sfb-koszul-generators-from-fibre-basis)

Proof plan:
1. Choose a finite Koszul-regular tuple `g` generating `I`. Localize at `p`.
   By [lem-weil-pbc-localization-flat] and [lem-sc-koszul-regular-flat-base-change],
   its image is Koszul-regular. By [lem-sc-koszul-conormal-basis], its conormal
   classes form a basis of `I_p / I_p^2` over `A_p / I_p`.
2. Since `I ≤ p`, reduce this basis modulo the maximal ideal. In coordinates the
   maximal-ideal multiple consists of vectors with entries in that ideal, so the
   images of `g` form a residue-field basis of `I_p / p I_p`. Comparing with the
   given basis shows that the length of `g` equals `r`.
3. Write `f = C g` with coefficients in `A`. Modulo `p`, `C` is the change matrix
   between the two fibre bases. Thus `s = det C` is outside `p`.
4. In `Localization.Away s`, the adjugate formula inverts `C`. The identities
   `f = C g` and `g = C⁻¹ f` show that `f` generates the extended ideal.
5. Flat base change makes `g` Koszul-regular over this localization; then
   [lem-sfb-koszul-equal-length-generators] makes the equal-length tuple `f`
   Koszul-regular as well.
6. If `r = 0`, basis comparison forces the original length to be zero and `I = 0`;
   the empty determinant is `1`, giving `s = 1`. A prime is proper, so its residue
   field is nonzero. The zero ring has no prime. No Noetherianity is used. -/
theorem exists_notMem_isKoszulRegular_of_fibre_basis
    (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime] (I : Ideal A)
    (hIp : I ≤ p)
    (hI : ∃ (m : ℕ) (g : Fin m → A),
      Ideal.span (Set.range g) = I ∧ RingTheory.Sequence.IsKoszulRegular g)
    (r : ℕ) (f : Fin r → I)
    (hf : ∃ b : Module.Basis (Fin r) p.ResidueField (p.ResidueField ⊗[A] I),
      ∀ i : Fin r, b i = (1 : p.ResidueField) ⊗ₜ[A] f i) :
    ∃ s : A, s ∉ p ∧
      Ideal.span (Set.range (fun i : Fin r ↦
        algebraMap A (Localization.Away s) (f i : A))) =
          I.map (algebraMap A (Localization.Away s)) ∧
      RingTheory.Sequence.IsKoszulRegular
        (fun i : Fin r ↦ algebraMap A (Localization.Away s) (f i : A)) := by
  sorry

end Ideal
