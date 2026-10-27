/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.RingTheory.TraceOneInvariantFiniteness
import Sheaf.RingTheory.AdicCompleteSubideal
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Artinian.Module
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp

/-! # Tame fixed rings and their generic components

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IV, Proposition 2.2.3
and paragraph 2.2.4, printed pp.53--54
(blueprint: lem-per-tame-fixed-ring-generic-components).

`B` is named by its equality to Mathlib's fixed subring. Prime residue fields
`q.ResidueField` are Mathlib's fraction fields of `C/q`. The algebra structures
in the component clause are fixed by equality to the canonical residue-field map.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace FixedPoints

/-- Tame invariants preserve the complete reduced local equidimensional structure;
residue and generic component field extensions are finite separable.

Source: ILO, Travaux de Gabber, Exposé IV, Proposition 2.2.3(i)(a)--(c), (ii)(a)--(b),
its proof and paragraph 2.2.4, printed pp.53--54
(blueprint: lem-per-tame-fixed-ring-generic-components).

Proof (the eight steps of the DAG):
1. The order d of H is a unit in C since its residue is a unit. Its inverse u is
   invariant and has group trace one. Apply
   lem-per-trace-one-noetherian-invariant-finiteness to obtain Noetherianity of B
   and module-finiteness of C over B, without assuming a faithful action.
2. The Reynolds operator E(c) = u sum_h h(c) is B-linear and retracts C onto B.
   Thus JC intersect B = J. Reducedness passes to B. The inverse of an invariant
   unit is invariant, so B is local with maximal ideal n = m intersect B.
   Reduction embeds B/n in k^H. Averaging any lift of an invariant residue proves
   surjectivity, giving the specified residue-field isomorphism.
3. Apply lem-sfb-adic-complete-subideal to nC contained in m, finitely generated
   by Noetherianity. Lift any compatible family in B/n^t to its limit c in C;
   E(c) lifts that family in B. Separatedness passes from C to B. Hence B is
   n-adically complete, as in def-weil-pbc-adically-complete-ring.
4. Pass to the faithful image of H in Aut(k). By
   lem-wf-finite-field-action-fixed-degree, k/k^H is finite separable.
5. By lem-dl-a1-finite-invariant-prime-orbits-residues the extension is integral
   and H acts transitively on primes with a fixed contraction. Choose a minimal
   prime below the contraction of q (lem-weil-pbc-prime-contains-minimal-prime),
   lift it by lem-weil-pbc-integral-injective-lying-over and apply pqf-lem-going-up.
   Transitivity and minimality of q show its contraction is minimal. Conversely
   lie over any minimal prime of B and choose a minimal prime below its lift.
6. For r = q intersect B, lem-weil-pbc-minimal-prime-reduced-localization-field
   identifies B_r with K = Frac(B/r). By lem-weil-pbc-localization-base-change,
   K tensor_B C is a reduced finite-dimensional K-algebra. Apply
   lem-weil-pbc-finite-dim-algebra-artinian and
   lem-sfb-reduced-artinian-residue-product to express it as a product of fields.
   By lem-weil-pbc-localization-spectrum-embedding the factor selected by q is
   Frac(C/q).
7. By lem-per-tame-invariants-arbitrary-base-change the invariant subring of this
   product is K. Transitivity on factors identifies K with L^D, where D is the
   stabilizer of the selected field L: an invariant tuple is determined by its
   selected coordinate, and the inverse transports that coordinate by H. Passing
   to the faithful image of D, lem-wf-finite-field-action-fixed-degree proves
   L/K finite separable for the canonical induced inclusion.
8. The injective component quotient map is integral. Apply
   lem-weil-pbc-integral-injective-dimension-equal to obtain dim(B/r) = dim(C/q) = e.
   Step 5 gives every component of B this way. Any chain of primes of B lies
   above a minimal prime and hence has length at most e; conversely chains in a
   component lift to B. Thus dim(B) = e and B is equidimensional. -/
theorem tame_fixed_ring_generic_components
    (C : Type u) [CommRing C] [IsReduced C]
    [IsNoetherianRing C] [IsLocalRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (p : ℕ) [CharP C p] (hp : 0 < p)
    (e : ℕ) (he : 1 ≤ e)
    (hdim : ringKrullDim C = e)
    (hequidim : ∀ q : Ideal C, q ∈ minimalPrimes C → ringKrullDim (C ⧸ q) = e)
    (H : Type v) [Group H] [Finite H] [MulSemiringAction H C]
    (htame : IsUnit (Nat.card H : IsLocalRing.ResidueField C))
    (B : Subring C) (hB : B = FixedPoints.subring C H) :
    IsReduced B ∧ IsNoetherianRing B ∧ Module.Finite B C ∧
    (∃ _ : IsLocalRing B,
      IsLocalRing.maximalIdeal B = (IsLocalRing.maximalIdeal C).comap B.subtype ∧
      IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      ∃ f : IsLocalRing.ResidueField B ≃+*
          FixedPoints.subfield H (IsLocalRing.ResidueField C),
        ∀ b : B, (f (IsLocalRing.residue B b) : IsLocalRing.ResidueField C) =
          IsLocalRing.residue C (b : C)) ∧
    Module.Finite (FixedPoints.subfield H (IsLocalRing.ResidueField C))
      (IsLocalRing.ResidueField C) ∧
    Algebra.IsSeparable (FixedPoints.subfield H (IsLocalRing.ResidueField C))
      (IsLocalRing.ResidueField C) ∧
    (∀ q : Ideal C, q ∈ minimalPrimes C → q.comap B.subtype ∈ minimalPrimes B) ∧
    (∀ r : Ideal B, r ∈ minimalPrimes B →
      ∃ q : Ideal C, q ∈ minimalPrimes C ∧ q.comap B.subtype = r) ∧
    (∀ q : PrimeSpectrum C, q.asIdeal ∈ minimalPrimes C →
      ringKrullDim (B ⧸ q.asIdeal.comap B.subtype) = e ∧
      ∃ a : Algebra (q.asIdeal.comap B.subtype).ResidueField q.asIdeal.ResidueField,
        algebraMap (q.asIdeal.comap B.subtype).ResidueField q.asIdeal.ResidueField =
          Ideal.ResidueField.map (q.asIdeal.comap B.subtype) q.asIdeal B.subtype rfl ∧
        Module.Finite (q.asIdeal.comap B.subtype).ResidueField q.asIdeal.ResidueField ∧
        Algebra.IsSeparable (q.asIdeal.comap B.subtype).ResidueField q.asIdeal.ResidueField) ∧
    ringKrullDim B = e ∧
    (∀ r : Ideal B, r ∈ minimalPrimes B → ringKrullDim (B ⧸ r) = e) := by
  sorry

end FixedPoints
