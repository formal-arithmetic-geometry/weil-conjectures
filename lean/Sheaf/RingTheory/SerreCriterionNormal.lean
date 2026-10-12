/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.RingTheory.SerreConditions
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.RingTheory.Depth
import Sheaf.RingTheory.KollarLocalDichotomy
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso
import Sheaf.RingTheory.NonzerodivisorIfMaximalNotAssociated
import Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Sheaf.RingTheory.RegularLocalDimOneIffNormal
import Sheaf.RingTheory.SerreCriterionReduced

/-!
# Serre's criterion for normality

Source: Stacks Project, Algebra, Lemma 10.157.4 (Tag 031S)
(blueprint: lem-weil-pbc-serre-criterion-normal).
-/

@[expose] public section

universe u

namespace Ring

/-- A Noetherian ring is normal if and only if it satisfies `(R₁)` and `(S₂)`.
Source: Stacks Project, Algebra, Lemma 10.157.4 (Tag 031S)
(blueprint: lem-weil-pbc-serre-criterion-normal).

Proof:
1. Localizations inherit Serre's conditions: primes of `Rₚ` come from primes `q ≤ p`,
   and their localizations are isomorphic to `R_q`
   (`lem-weil-pbc-localization-prime-residue-field-iso`). Dimension, depth and regularity
   are invariant under these isomorphisms; localization preserves Noetherianity.
2. For a normal local domain of dimension zero, the maximal ideal is zero, so the ring is
   regular and has depth at least zero. In dimension one, regularity follows from
   `lem-weil-pbc-regular-local-dim-one-iff-normal`; a nonzero element of the maximal ideal
   is a nonzerodivisor and gives depth at least one.
3. In dimension at least two, apply `lem-weil-pbc-kollar-local-dichotomy`. The Artinian
   and dimension-one cases are excluded. In its finite-extension case, the kernel is killed
   by a power of the maximal ideal and hence zero. Choose a nonzerodivisor `x` on the finite
   extension in the maximal ideal (`lem-weil-pbc-nonzerodivisor-if-maximal-not-associated`).
   Multiplication by a power of `x` embeds the extension into the common fraction field.
   Finiteness makes its elements integral (`lem-weil-pbc-finite-algebra-is-integral`),
   so integral closedness forces the extension to equal the original ring, a contradiction.
   Only the depth-at-least-two case remains.
4. Steps 2 and 3 at every prime give `(R₁)` and `(S₂)`.
5. Conversely, reduce to local rings and use strong induction on their finite dimension
   (`lem-weil-pbc-noetherian-local-system-of-parameters`). Conditions `(R₁)` and `(S₂)`
   imply `(R₀)` and `(S₁)`, hence reducedness (`lem-weil-pbc-serre-criterion-reduced`).
   Dimension zero gives a field; dimension one gives a normal domain by the same
   dimension-one criterion.
6. In higher dimension, reduced Noetherian rings have finitely many minimal primes. By
   `lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions`, it suffices to prove
   integral closedness in the total fraction ring. For an integral element `z`, the algebra
   `A[z]` is finite (`lem-weil-pbc-finite-of-integral-generators`).
7. Induction identifies this extension with `A` at every nonmaximal prime. Clearing
   denominators of its finitely many generators shows the conductor is contained in no
   nonmaximal prime.
8. Unless the extension equals `A`, the conductor has radical the maximal ideal
   (`lem-weil-pbc-zero-locus-eq-iff-radical-eq`); finite generation then gives a power of
   the maximal ideal killing `A[z]/A` (`lem-weil-pbc-fg-ideal-radical-power`).
9. Condition `(S₂)` supplies a nonzerodivisor in the maximal ideal, which is a unit in the
   total fraction ring. Thus the maximal ideal is not associated to `A[z]`. A proper finite
   extension as in step 8 would give the finite-extension case of the local dichotomy,
   incompatible with depth at least two. Hence `z` lies in `A`, completing the induction
   and proving that every prime localization is a normal domain. -/
theorem serreCriterionNormal (R : Type u) [CommRing R] [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
    IsSerreR R 1 ∧ IsSerreS R 2 := by
  sorry

end Ring
