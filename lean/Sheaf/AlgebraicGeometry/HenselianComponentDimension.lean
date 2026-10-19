/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.IndEtaleUniverseTransport
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Sheaf.TraceFormula.IndEtaleLocalHenselianIntegral
import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# One-dimensional components of a henselian local scheme

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIV, Lemma 2.1.5,
printed page 210 (blueprint: lem-per-henselian-component-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A Noetherian henselian local scheme has a one-dimensional irreducible component
if and only if its strict localization at a geometric closed point has one.
Source: ILO, Travaux de Gabber, Expose XIV, Lemma 2.1.5, printed page 210
(blueprint: lem-per-henselian-component-dimension).

Proof, following the six steps of the DAG node:
1. Write B for the strict-henselization ring and f : A → B for its structural map.
   The etale-local-ring-triples comparison identifies the pointed-neighbourhood colimit
   with the triples colimit for the maximal ideal and the separable residue closure
   inside Ω. Strict-henselization-triples makes B henselian local and ind-etale over A,
   with maximal ideal contracting to the maximal ideal of A. The theorem
   lem-sc-strict-henselization-faithfully-flat makes f faithfully flat, hence flat.
2. Apply lem-trf-ind-etale-local-henselian-integral to obtain integrality over the
   ordinary henselization H of A at its maximal ideal. Localization at that maximal
   ideal is A, since its denominators are units. Henselianity of A and the universal
   property in def-weil-pbc-henselization-at-prime identify H with A: construct the
   retraction and use uniqueness for the other composite. Pull the coefficients of
   each monic equation back along this isomorphism to obtain integrality over A.
   Faithfully-flat-universally-injective applied to the module A makes f injective.
3. Flat-going-down shows that the contraction of a minimal prime q of B is minimal
   in A: a smaller prime downstairs lifts to a prime below q and hence must be equal.
4. For a minimal prime p of A, integral-injective-lying-over gives a prime Q over p.
   Prime-contains-minimal-prime gives a minimal q contained in Q. Its contraction is
   contained in p, and therefore equals p. No uniqueness of such q is required.
5. The induced map A/p → B/q is injective by the definition of contraction and integral
   by reducing the monic equations from step 2. Apply
   lem-weil-pbc-integral-injective-dimension-equal to identify their Krull dimensions.
6. Spec-irreducible-components-minimal-primes identifies components with V(p) and V(q).
   Spec-quotient-homeomorphism-zero-locus identifies these subspaces with the quotient
   spectra, whose topological dimensions equal their ring dimensions. Step 3 gives
   the implication from a component upstairs; step 4 gives the reverse implication;
   step 5 preserves dimension one in both directions. -/
theorem henselian_has_one_dimensional_component_iff_strictHenselization
    (A : Type u) [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barX : Spec (.of Ω) ⟶ Spec (.of A))
    (hbarX : barX (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint A) :
    (∃ C ∈ irreducibleComponents (Spec (.of A)), topologicalKrullDim C = 1) ↔
      ∃ C ∈ irreducibleComponents (strictHenselizationScheme barX),
        topologicalKrullDim C = 1 := by
  sorry

end AlgebraicGeometry.Scheme
