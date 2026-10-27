/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Filtration
import WeilConjectures.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods
import WeilConjectures.RingTheory.HenselizationStageMap
import WeilConjectures.RingTheory.HenselianFactorizationCriterion

/-!
# Unique lifting from completions into a henselian target

Source: Stacks Project, Restricted Power Series, Tag 0AKJ
(`lemma-fully-faithful-etale-over-complement`), specialized to a henselian target.
(blueprint: lem-per-etale-away-completion-hom-lifting)
-/

@[expose] public section

universe u v

namespace RingTheory

/-- A map of completions uniquely algebraizes when the source is finite type and etale
away from the completion ideal and the Noetherian target is a henselian pair.
Source: Stacks Project, Restricted Power Series, Tag 0AKJ
(`lemma-fully-faithful-etale-over-complement`), henselian-target specialization.
(blueprint: lem-per-etale-away-completion-hom-lifting)

The conclusion uses the node's equivalent restriction equation. Every A-algebra map
preserves the powers of the extended ideal, so equality on D determines the entire
map on completions; thus the completion of the unique u is exactly phi.

Proof (the seven steps of the DAG node):
1. By lem-weil-pbc-module-completion-complete, projections of completions onto the
   quotients are onto, with kernels the corresponding ideal powers. Since A is
   Noetherian, I is finitely generated. An A-algebra map preserves these powers.
   Approximate each completed element at level n by an element of D: this shows
   that phi is determined by its restriction and identifies the restriction equation
   with equality of the completed maps.
2. Put E = D tensor_A C and J = IC. Finite generation and
   lem-weil-pbc-finite-type-algebra-noetherian make E Noetherian. By
   lem-weil-pbc-etale-scheme-base-change, E is etale off V(J). The maps
   d tensor c |-> phi_n(d)c on quotients give a completed retraction
   sigma : E-completion -> C-completion, restricting on D to phi.
3. Lem-per-completed-retraction-conormal-torsion annihilates the conormal of
   ker(sigma) by a power of J. Apply lem-per-conormal-torsion-algebraization
   with base ring and finite type algebra both E, retaining the E-algebra structure.
   This gives a finite type E-algebra T and an E-algebra isomorphism
   beta : T-completion -> C-completion. T is finite type over C, hence Noetherian
   by lem-weil-pbc-finite-type-algebra-noetherian.
4. Lem-weil-pbc-module-completion-complete identifies all structural quotient maps
   C/J^n -> T/J^nT as isomorphisms: beta induces their inverses. Apply
   lem-weil-pbc-etale-infinitesimal-neighbourhoods to obtain an etale open W in
   Spec T containing V(JT).
5. Write the complement of W as V(L). Since L + JT = T, choose g in L congruent
   to 1 modulo JT. Then Spec T_g lies in W; by
   lem-weil-pbc-etale-composition-cancellation, C -> F = T_g is etale.
   The element g is a unit modulo every J^n, so localization preserves the quotients
   and beta gives F-completion isomorphic to C-completion.
6. Lem-weil-pbc-henselization-stage-map supplies the unique C-algebra map
   tau : F -> C. The target completion is complete by
   lem-weil-pbc-module-completion-complete and henselian by
   lem-weil-pbc-complete-pair-henselian. Uniqueness in the stage-map lemma makes
   the two maps F -> C-completion, induced by tau and beta, equal. The composite
   D -> E -> T -> F -> C is the required u, with the stated restriction equation.
7. Lem-weil-pbc-henselian-factorization-criterion puts J in the Jacobson radical
   of C. Lem-weil-pbc-krull-intersection-jacobson applied to the finite C-module C
   makes C -> C-completion injective. Two lifts have equal composites with this
   injection by step 1, so they agree pointwise. -/
theorem existsUnique_algHom_lift_of_etale_away_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (D : Type u) [CommRing D] [Algebra A D]
    (hD : (algebraMap A D).FiniteType)
    (hEtale : AlgebraicGeometry.Etale
      (AlgebraicGeometry.morphismRestrict
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A D)))
        ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
          (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩))
    (C : Type v) [CommRing C] [Algebra A C] [IsNoetherianRing C]
    [HenselianRing C (I.map (algebraMap A C))]
    (φ : AdicCompletion (I.map (algebraMap A D)) D →ₐ[A]
      AdicCompletion (I.map (algebraMap A C)) C) :
    ∃! u : D →ₐ[A] C, ∀ d : D,
      algebraMap C (AdicCompletion (I.map (algebraMap A C)) C) (u d) =
        φ (algebraMap D (AdicCompletion (I.map (algebraMap A D)) D) d) := by
  sorry

end RingTheory
