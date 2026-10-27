/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import WeilConjectures.RingTheory.AnnihilatorAssociatedPrimes
import Sheaf.RingTheory.UniversalInjectiveCheckStalks
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Universal injectivity from coverage of relative associated primes

Source: Stacks Project, More on Flatness, Tag 05DH,
`lemma-base-change-universally-flat`
(blueprint: lem-sfb-assassin-cover-universal-section-injection).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

open scoped TensorProduct

namespace RingTheory

/-- A flat algebra map whose spectrum covers the associated primes in every relevant
residue-field fibre gives a universally injective section map. The map in the conclusion
sends `p ⊗ l` to `(p ⊗ 1) ⊗ l`; no faithful-flatness hypothesis is imposed.

Source: Stacks Project, More on Flatness, Tag 05DH,
`lemma-base-change-universally-flat`
(blueprint: lem-sfb-assassin-cover-universal-section-injection).

Proof, following the four steps of the DAG node:
1. Apply `lem-trf-universal-injective-check-stalks` to the C-linear section map.
   Tensor symmetry identifies its left-tensor test with the right-tensor test here.
   It suffices to establish universal injectivity over R_p at each prime q of C.
2. Localize R, C, D and P at p = q ∩ R and q. The induced R_p -> C_q map is
   local and essentially finitely presented, by localizing a finite presentation of C.
   Localizing a finite presentation of P makes P_q finitely presented over C_q.
   `lem-pc-affine-flat-module-localization-preserves-flatness` and
   `lem-weil-pbc-flat-over-localization` give flatness of P_q over R_p and of D_q
   over C_q. The canonical tensor-localization isomorphism sends
   `(x/s) ⊗ (d/t)` to `(x ⊗ d)/(st)` and identifies the section maps.
3. The fibre ring over κ(p) is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`. Identify the localized fibre with
   P_q/pP_q. Given an associated prime of this module, clear the finitely many
   denominators of generators of its contracted ideal in the fibre ring: multiplying
   the witnessing element by their product realizes the contracted prime as an
   element annihilator before localization. The coverage hypothesis lifts that prime
   to D. It misses C minus q, so `lem-weil-pbc-localization-spectrum-embedding`
   lifts it to D_q; injectivity of contraction identifies its image in C_q with
   the specified associated prime.
4. Apply `lem-sfb-assassin-cover-universal-section-injection-local` (Tag 05DG) to
   R_p -> C_q -> D_q and P_q. Steps 2 and 3 verify all its hypotheses. This proves
   universal injectivity at every q, and step 1 gives the conclusion.
-/
theorem section_rTensor_injective_of_relative_associatedPrimes_covered
    (R : Type u) (C : Type v) (D : Type w) (P : Type x)
    [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra C D]
    [AddCommGroup P] [Module C P] [Module R P] [IsScalarTower R C P]
    [Algebra.FinitePresentation R C] [Module.FinitePresentation C P]
    [Module.Flat R P] [Module.Flat C D]
    (hcover : ∀ (p : PrimeSpectrum R) (q : PrimeSpectrum C),
      q.asIdeal.comap (algebraMap R C) = p.asIdeal →
      q.asIdeal ∈ annihilatorAssociatedPrimes C (P ⊗[R] p.asIdeal.ResidueField) →
      q ∈ Set.range (PrimeSpectrum.comap (algebraMap C D))) :
    ∀ (L : Type (max u v w x y)) [AddCommGroup L] [Module R L],
      Function.Injective
        ((((TensorProduct.mk C P D).flip (1 : D)).restrictScalars R).rTensor L) := by
  sorry

end RingTheory
