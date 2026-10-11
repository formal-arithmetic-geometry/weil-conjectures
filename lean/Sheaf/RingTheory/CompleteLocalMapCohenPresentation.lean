/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.RingTheory.CohenRing
public import Sheaf.RingTheory.IsRegularSystemOfParameters

/-!
# Compatible Cohen presentations of complete local homomorphisms

Source: Stacks Project, Lemma 07NN and the proof of Proposition 07NQ
(blueprint: lem-weil-pbc-complete-local-map-cohen-presentation).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A complete local homomorphism admits compatible power-series presentations with a flat
map carrying parameters into parameters and regular closed fibre. Source: Stacks, Lemma 07NN;
the first parameter in positive residue characteristic is chosen as in Proposition 07NQ
(blueprint: lem-weil-pbc-complete-local-map-cohen-presentation).

Proof for stage 3:
1. Use `lem-weil-pbc-cohen-power-series-presentation` to present A and B by power-series
rings R and S₀ over fields or Cohen rings. By
`lem-weil-pbc-power-series-field-cohen-regular-complete` they are regular, complete and local;
the surjection S₀ → B has kernel J contained in the maximal ideal.
2. Lift fq to φ : R → S₀ using `lem-weil-pbc-field-cohen-power-series-formally-smooth` and
`lem-weil-pbc-fs-adic-lift-into-complete`. The kernel J is closed, since completeness of B
makes the intersection of its maximal-ideal powers zero. The lift maps maximal ideals into
maximal ideals.
3. Adjoin variables Y to S₀ and let S = Λ_B[[Y,Z]]. Set v(Y) = 0 and set
u(X_i) = φ(X_i) + Y_i, using `lem-weil-pbc-power-series-adic-evaluation`.
The uniqueness clause of that lemma gives vu = fq; quotienting the Y variables uses
`lem-weil-pbc-power-series-quotient-variables`.
4. The images of the parameters of R, followed by the Z variables, generate the maximal
ideal of S: they generate each φ(X_i), hence each Y_i. Their number equals dim S. In the
Cohen case the list starts with p. Thus the images extend to a regular system of parameters.
5. By `lem-weil-pbc-regular-local-generators-regular-sequence`, the initial segment is a
regular sequence and its quotient is regular local. Apply `lem-weil-pbc-flat-over-regular`
to obtain flatness. The quotient is S modulo the extension of the maximal ideal of R.
This includes the empty parameter list.
-/
theorem exists_complete_local_map_cohen_presentation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    ∃ (ΛA ΛB : Type (max u v)) (_ : CommRing ΛA) (_ : CommRing ΛB) (n m : ℕ),
      let R := MvPowerSeries (Fin n) ΛA
      let S := MvPowerSeries (Fin m) ΛB
      ∃ (_ : IsRegularLocalRing R) (_ : IsRegularLocalRing S),
        IsAdicComplete (IsLocalRing.maximalIdeal R) R ∧
        IsAdicComplete (IsLocalRing.maximalIdeal S) S ∧
        (CharZero (IsLocalRing.ResidueField A) → IsField ΛA ∧ IsField ΛB) ∧
        (∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
          IsCohenRing p ΛA ∧ IsCohenRing p ΛB) ∧
        ∃ (q : R →+* A) (v : S →+* B) (u : R →+* S),
          Function.Surjective q ∧ IsLocalHom q ∧
          Function.Surjective v ∧ IsLocalHom v ∧ IsLocalHom u ∧
          v.comp u = f.comp q ∧ u.Flat ∧
          IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map u) ∧
          ∃ (t : List R) (z : List S),
            IsLocalRing.IsRegularSystemOfParameters t ∧
            IsLocalRing.IsRegularSystemOfParameters (t.map u ++ z) ∧
            (∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
              t.head? = some (p : R)) :=
  sorry

end RingHom
