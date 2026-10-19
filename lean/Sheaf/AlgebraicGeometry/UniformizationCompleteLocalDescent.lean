/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.AlterationCoverCalculus
import Sheaf.AlgebraicGeometry.CompletelyDecomposedEtaleFiniteSubcover
import Sheaf.RingTheory.CompleteLocalExcellent
import WeilConjectures.RingTheory.CompletionDimension
import Sheaf.RingTheory.HenselianPairApproximation
import Mathlib.RingTheory.FinitePresentation
import Sheaf.RingTheory.HenselianNormalCompletionPreparation

/-!
# Descent of regular alteration coverings from complete local bases

Source: ILO, Travaux de Gabber, Expose III Proposition 6.2, printed pp. 43--45;
bounded use in Expose IX 1.3, p. 132
(blueprint: lem-per-uniformization-complete-local-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The proposition U_ell(S,Z): a finite alteration covering by regular Noetherian schemes,
with strict normal crossings boundaries having exactly the inverse-image supports.
The identity object is specified by its underlying object of `Over S`; no choice of an
alteration object or boundary is built into the proposition. Empty families of boundary
components and empty covering families are permitted.
Source: ILO III 6.1--6.2, pp. 43--45
(blueprint: lem-per-uniformization-complete-local-descent). -/
def HasRegularAlterationCover (ell : ℕ) [Fact ell.Prime]
    (S : Scheme.{u}) [IsNoetherian S] (Z : Set S) : Prop :=
  ∃ base : PrimeToEllAlteration.Alt S,
    base.obj = Over.mk (𝟙 S) ∧
    ∃ (n : ℕ) (T : Fin n → PrimeToEllAlteration.Alt S) (q : ∀ i, T i ⟶ base),
      PrimeToEllAlteration.IsCoveringFamily ell T q ∧
      (∀ i, IsRegularScheme (T i).obj.left ∧ IsNoetherian (T i).obj.left) ∧
      ∀ i, ∃ H : (T i).obj.left.IdealSheafData,
        IsStrictNormalCrossingsBoundary H ∧
        (H.support : Set (T i).obj.left) = (T i).obj.hom ⁻¹' Z

/-- Complete normal local uniformization implies uniformization for reduced quasi-excellent
Noetherian schemes, both without a dimension bound and with any fixed nonnegative bound.
Normal complete local bases are spectra of integrally closed local domains complete for
powers of their maximal ideal. Bounds use the topological Krull dimension, including
minus infinity for the empty scheme.
Source: ILO III Proposition 6.2, pp. 43--45, and IX 1.3, p. 132
(blueprint: lem-per-uniformization-complete-local-descent).

Proof plan, following the seven steps of the node:
1. For a normal excellent henselian local ring, use
   lem-per-henselian-normal-completion-preparation to obtain a normal local completion
   and a nowhere dense pulled-back closed subset. Complete-local excellence permits
   application of the complete-normal-local hypothesis.
2. Apply lem-per-marked-finite-diagram-approximation to the finite covering, its boundary
   components, intersections and inclusions. Apply lem-per-alteration-cover-approximation
   to the same model. Enlarge the index and take the maximum congruence threshold.
3. The Noetherian finite-type finite-presentation lemma gives finitely many equations
   for the model algebra. Henselian-pair approximation supplies a simultaneous solution
   over the original ring, congruent to the completed solution to the required order.
4. Induct strongly on the local dimension. The approximations are regular with the
   required boundaries near the entire closed fibres. At nonclosed points use the
   smaller-dimensional case and lem-per-henselian-regular-pair-spreading. Extract a
   finite completely decomposed etale family on the punctured scheme by
   lem-per-completely-decomposed-etale-finite-subcover. Apply the dimension-inductive
   gluing lemma lem-per-alteration-cover-closed-fibre-shrink to combine these coverings
   with the closed-fibre neighborhoods. No arbitrary open shrinking is asserted to cover.
5. At each point of a reduced quasi-excellent Noetherian scheme take its ordinary
   henselization and finite componentwise normalization by the preparation lemma.
   Apply the local result to its normal henselian local factors. The component family,
   normalization maps and these coverings compose by alteration-cover calculus.
6. Spread the resulting regular marked coverings to pointed etale neighborhoods with
   unchanged residue fields. The finite-subcover lemma extracts finitely many, and
   alteration-cover calculus composes their finite coverings to give the desired one.
7. For dimension at most d, henselization preserves local dimension, normalization does
   not increase it, and completion preserves it by lem-weil-pbc-completion-dimension.
   Thus only complete normal local bases of dimension at most d enter the argument.
   Without a bound perform the argument pointwise, with no common dimension bound.
   The empty scheme uses the empty covering; empty markings and dimension zero cause
   no exceptions. -/
theorem uniformization_complete_local_descent (ell : ℕ) [Fact ell.Prime] :
    ((∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
        [IsDomain A] [IsIntegrallyClosed A]
        [IsAdicComplete (IsLocalRing.maximalIdeal A) A],
        IsUnit (ell : A) → ∀ Z : Set (Spec (.of A)),
          IsClosed Z → IsNowhereDense Z →
            HasRegularAlterationCover ell (Spec (.of A)) Z) →
      ∀ (S : Scheme.{u}) [IsReduced S] [IsNoetherian S],
        (∀ U : S.affineOpens, IsQuasiExcellent Γ(S, U)) →
        (∀ s : S, IsUnit (ell : S.presheaf.stalk s)) →
        ∀ Z : Set S, IsClosed Z → IsNowhereDense Z →
          HasRegularAlterationCover ell S Z) ∧
    (∀ d : ℕ,
      (∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
          [IsDomain A] [IsIntegrallyClosed A]
          [IsAdicComplete (IsLocalRing.maximalIdeal A) A],
          topologicalKrullDim (Spec (.of A)) ≤ d →
          IsUnit (ell : A) → ∀ Z : Set (Spec (.of A)),
            IsClosed Z → IsNowhereDense Z →
              HasRegularAlterationCover ell (Spec (.of A)) Z) →
        ∀ (S : Scheme.{u}) [IsReduced S] [IsNoetherian S],
          topologicalKrullDim S ≤ d →
          (∀ U : S.affineOpens, IsQuasiExcellent Γ(S, U)) →
          (∀ s : S, IsUnit (ell : S.presheaf.stalk s)) →
          ∀ Z : Set S, IsClosed Z → IsNowhereDense Z →
            HasRegularAlterationCover ell S Z) := by
  sorry

end AlgebraicGeometry
