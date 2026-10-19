/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.RingTheory.FormallySmoothAdic
import Sheaf.RingTheory.FormallySmoothAdicLift
import Sheaf.RingTheory.FormallySmoothAdicFlat
import Sheaf.RingTheory.CompleteLocalQuotient
import Sheaf.RingTheory.FormallySmoothAdicLiftIntoComplete
import Sheaf.RingTheory.ExistsLiftOfFieldCharP

/-!
# Perfect-residue coefficient DVR extension and local lifting

Source: Illusie–Laszlo–Orgogozo, *Travaux de Gabber*, Exposé IV, §4.2.5,
first two paragraphs, using §4.1.3–§4.1.6 (blueprint: lem-per-perfect-residue-coefficient-dvr).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.overlappingInstances false

universe u v w

namespace Algebra

/-- An unramified coefficient-DVR extension of a complete mixed-characteristic trait,
together with the compatible lifting property used in the Cohen–Gabber construction.

Source: Illusie–Laszlo–Orgogozo, *Travaux de Gabber*, Exposé IV, §4.2.5,
first two paragraphs (blueprint: lem-per-perfect-residue-coefficient-dvr).

Proof plan, following the six steps of the DAG node:

1. The perfect-base field extension `k'/k₀` is formally smooth without a finite-type
   assumption. Use `lem-weil-pbc-field-char-p-nilpotent-lifting` for a square-zero
   extension. The ring lift is `k₀`-linear: write each base element as a `p`-th power
   using perfectness; the difference of the lifted and prescribed images is a
   `p`-th power of an element of the square-zero ideal, hence zero.
2. A DVR is Noetherian, and the field `k'` is complete for its zero maximal ideal.
   Apply `lem-weil-pbc-fs-adic-lift-from-residue-field` to obtain a complete
   Noetherian local `V`, a formally smooth local map `ι`, and a compatible
   identification `V / π V ≃ k'`.
3. By `lem-weil-pbc-fs-adic-local-flat`, `V` is flat over `W`. Tensoring the
   injection given by multiplication by `π` shows that `ι π` is a nonzerodivisor.
   The field quotient gives `maximalIdeal V = (ι π)`. Using
   `lem-weil-pbc-dvr-unit-times-uniformizer-power`, every nonzero element of `W`
   maps to a unit times a nonzero power of `ι π`, so `ι` is injective.
4. Adic separatedness gives zero intersection of the powers of the maximal ideal.
   Every nonzero element of `V` therefore has a largest uniformizer exponent,
   and division by that power leaves a unit. Products of nonzero elements are
   nonzero. In every nonzero ideal, a member of least exponent generates the
   ideal; the zero ideal is principal too. Thus `V` is a local PID with nonzero
   maximal ideal, hence a DVR, complete by construction.
5. For the target `C`, put `J = (γ π)`. Locality gives `J ≤ maximalIdeal C`, so
   `J` is proper. By `lem-weil-pbc-complete-local-quotient`, `C / J` is complete.
   Its separatedness gives `J = ⋂ m ≥ 1, (J + (maximalIdeal C) ^ m)`, so `J`
   is closed. Also `J ^ 1 ≤ maximalIdeal C`; this includes `γ π = 0` and
   cases where `γ π` is a zerodivisor.
6. The map `g = s ∘ e ∘ residue V` is `W`-linear by the compatibility of `e`
   and the explicitly assumed base-linearity of `s`. It kills `maximalIdeal V`.
   Apply `lem-weil-pbc-fs-adic-lift-into-complete` with source ideal
   `maximalIdeal V`, target ideal `maximalIdeal C`, quotient ideal `J`, and
   exponents `r = t = 1`. This gives a `W`-linear lift into `C` carrying the
   source maximal ideal into the target maximal ideal. Units remain units,
   so the lift is local. Its residue map is the assumed isomorphism `q.comp s`.

Here `e` identifies the residue field of `V` with `k'`, and `q` is the canonical
map from `C / π C` to the residue field of `C`. The equation quantified over
`x : W` expresses the `k₀`-linearity of `s`, since `residue W` is surjective.
(blueprint: lem-per-perfect-residue-coefficient-dvr)
-/
theorem exists_perfect_residue_coefficient_dvr
    (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsNoetherianRing W] [IsLocalRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W]
    (p : ℕ) (hp : p.Prime)
    (hres : ringChar (IsLocalRing.ResidueField W) = p)
    (π : W) (hπ : π ≠ 0)
    (hπgen : IsLocalRing.maximalIdeal W = Ideal.span {π})
    [PerfectField (IsLocalRing.ResidueField W)]
    (k' : Type v) [Field k']
    [Algebra (IsLocalRing.ResidueField W) k'] :
    ∃ (V : Type (max u v)) (_ : CommRing V) (_ : IsDomain V)
      (_ : IsDiscreteValuationRing V) (_ : IsNoetherianRing V) (_ : IsLocalRing V)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V)
      (ι : W →+* V), IsLocalHom ι ∧ Function.Injective ι ∧
      (ι π ≠ 0) ∧ IsLocalRing.maximalIdeal V = Ideal.span {ι π} ∧
      (ringChar (IsLocalRing.ResidueField V) = p) ∧
      (∃ rι : IsLocalRing.ResidueField W →+* IsLocalRing.ResidueField V,
        rι.comp (IsLocalRing.residue W) = (IsLocalRing.residue V).comp ι ∧
        ∃ e : IsLocalRing.ResidueField V ≃+* k',
          e.toRingHom.comp rι = algebraMap _ k' ∧
      (@Algebra.FormallySmoothAdic W V _ _ (RingHom.toAlgebra ι)
        (IsLocalRing.maximalIdeal V)) ∧
      ∀ (C : Type w) (_ : CommRing C) (_ : IsNoetherianRing C) (_ : IsLocalRing C)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal C) C) (γ : W →+* C),
        IsLocalHom γ →
        ∀ (s : k' →+* C ⧸ Ideal.span {γ π})
          (q : C ⧸ Ideal.span {γ π} →+* IsLocalRing.ResidueField C),
          q.comp (Ideal.Quotient.mk (Ideal.span {γ π})) = IsLocalRing.residue C →
          (∀ x : W, s (algebraMap (IsLocalRing.ResidueField W) k'
            (IsLocalRing.residue W x)) = Ideal.Quotient.mk (Ideal.span {γ π}) (γ x)) →
          Function.Bijective (q.comp s) →
            ∃ f : V →+* C,
              f.comp ι = γ ∧ IsLocalHom f ∧
                (Ideal.Quotient.mk (Ideal.span {γ π})).comp f =
                  s.comp (e.toRingHom.comp (IsLocalRing.residue V))) := by
  sorry

end Algebra
