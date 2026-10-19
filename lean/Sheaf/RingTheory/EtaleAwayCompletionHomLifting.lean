/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Filtration
import Sheaf.RingTheory.ConormalTorsionAlgebraization
import Sheaf.AlgebraicGeometry.EtaleInfinitesimalNeighbourhoods
import WeilConjectures.RingTheory.HenselizationStageMap
import Sheaf.RingTheory.HenselianFactorizationCriterion
import Sheaf.RingTheory.CompletedRetractionConormalTorsion

/-!
# Unique lifting of completed maps into a henselian target

Source: Stacks Project, Restricted Power Series, Tag 0AKJ,
`lemma-fully-faithful-etale-over-complement`, specialized to a henselian target
(blueprint: lem-per-etale-away-completion-hom-lifting).

The conclusion uses the equivalent restriction formulation: the unique lift commutes
with the canonical completion maps. Finite generation of the ideal ensures that this
also identifies its completed map with the prescribed map on the entire completion.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open AlgebraicGeometry

namespace AdicCompletion

/-- Every map from the completion of a finite type algebra etale away from the ideal
into the completion of a Noetherian henselian target uniquely lifts to the target.
The displayed equation is the restriction of the prescribed map along D to its completion.

Source: Stacks Project, Tag 0AKJ, `lemma-fully-faithful-etale-over-complement`, specialized
using that the pair henselization of a henselian pair is itself
(blueprint: lem-per-etale-away-completion-hom-lifting).

Proof:
1. The ideal I is finitely generated since A is Noetherian. By
   `lem-weil-pbc-module-completion-complete`, completed modules are complete and their
   n-th quotient maps are onto with kernels I^n times the completion. An A-algebra map
   of completions preserves these powers. For each completed element x choose a d in D
   representing its n-th coordinate. Then x minus the image of d lies in the n-th power,
   so the n-th coordinate of its image is determined by d. Thus maps of completions are
   determined by restriction to D, and the displayed equation is equivalent to saying
   that the completed lift is the prescribed map.
2. Set E = D tensor_A C and J = IC. Finite type generators and
   `lem-weil-pbc-finite-type-algebra-noetherian` make E Noetherian. By
   `lem-weil-pbc-etale-scheme-base-change` it is etale off V(J). Tensor the compatible
   quotient maps of the prescribed map with C, then take their inverse limit to obtain
   a retraction sigma from the completion of E to the completion of C.
3. By `lem-per-completed-retraction-conormal-torsion`, a power of J annihilates the
   conormal of ker sigma. Apply `lem-per-conormal-torsion-algebraization` with base and
   finite type algebra both E. This gives a finite type E-algebra T and an E-algebra
   isomorphism beta from its completion to the completion of C. T is finite type over C
   and Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`.
4. By `lem-weil-pbc-module-completion-complete`, beta induces isomorphisms modulo every
   positive power of J. The structural maps from C to T induce their inverses. Apply
   `lem-weil-pbc-etale-infinitesimal-neighbourhoods` to obtain an etale open W in Spec T
   containing V(JT).
5. Write the closed complement as V(L). Since L + JT = T, choose g in L congruent to 1
   modulo JT. Localize to F = T_g; its spectrum lies in W, so F is etale over C by
   `lem-weil-pbc-etale-composition-cancellation`. The geometric series in 1-g makes g
   invertible modulo every positive power of J, so all quotients and beta are unchanged.
6. By `lem-weil-pbc-henselization-stage-map`, F has a unique C-algebra map tau to C.
   Completeness and `lem-weil-pbc-complete-pair-henselian` make the completion of C a
   henselian target too. Uniqueness in the stage-map lemma identifies the completion
   map composed with tau with beta on F. Compose D to E to T to F with tau. E-linearity
   of beta gives the displayed equation; Step 1 identifies the completed map with phi.
7. By `lem-weil-pbc-henselian-factorization-criterion`, J lies in the Jacobson radical
   of C. By `lem-weil-pbc-krull-intersection-jacobson`, its powers have zero intersection
   in C. Hence the completion map of C is injective. Two lifts satisfying the displayed
   equation therefore agree on every d, proving uniqueness. -/
theorem existsUnique_algHom_of_etale_away_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (D : Type u) [CommRing D] [Algebra A D]
    (hD : RingHom.FiniteType (algebraMap A D))
    (hetale : Etale (Spec.map (CommRingCat.ofHom (algebraMap A D)) ∣_
      ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
        (PrimeSpectrum.isClosed_zeroLocus (I : Set A)).isOpen_compl⟩))
    (C : Type v) [CommRing C] [Algebra A C] [IsNoetherianRing C]
    [HenselianRing C (I.map (algebraMap A C))]
    (φ : AdicCompletion (I.map (algebraMap A D)) D →ₐ[A]
      AdicCompletion (I.map (algebraMap A C)) C) :
    ∃! f : D →ₐ[A] C, ∀ d : D,
      algebraMap C (AdicCompletion (I.map (algebraMap A C)) C) (f d) =
        φ (algebraMap D (AdicCompletion (I.map (algebraMap A D)) D) d) := by
  sorry

end AdicCompletion
