/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.CompletionDimension
import Sheaf.RingTheory.NormalOfFlatNormalFibers
import Sheaf.RingTheory.GRingCompletionRegular
import Sheaf.RingTheory.RegularRingNormal
import Sheaf.RingTheory.SerreCriterionNormal
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.GRing
import WeilConjectures.RingTheory.SerreConditions

/-!
# Local data at singular points of an excellent normal surface

Source: Stacks Project, More on Algebra, Tags 07QT, 07QU, 0C23 and 07NV;
Algebra, Tag 031S; Resolution of Surfaces, proof of Tag 0BGP
(blueprint: lem-per-excellent-normal-surface-local-data).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- The regular locus of an excellent normal integral Noetherian surface is open and its
complement is a finite set of closed points. Each singular stalk is an excellent normal
Noetherian local domain of dimension two, and its maximal-ideal completion is a complete
normal Noetherian local domain of dimension two.

Source: Stacks Project, Tags 07QT, 07QU, 0C23, 07NV and 031S, and the normal-surface
argument in the proof of Tag 0BGP
(blueprint: lem-per-excellent-normal-surface-local-data).

Proof plan:
1. Choose a finite affine Noetherian cover. Identify every stalk with the corresponding
   prime localization by lem-weil-pbc-affine-open-stalk-localization. It is Noetherian by
   lem-weil-pbc-localization-noetherian and normal by the normality hypothesis.
2. On each chart, apply the J-2 clause of def-exc-excellent-ring to the identity finite
   type algebra. The resulting open regular loci glue, so the singular locus is closed.
3. Every affine open has dimension at most two: take closures of its irreducible closed
   chains in X. Strictness is preserved by intersection with the open. Prime localization
   (lem-weil-pbc-primes-of-localization) and the affine stalk identification give the same
   bound for every stalk, using def-kun-topological-krull-dimension and
   lem-weil-pbc-spec-irreducible-closed-subsets-primes.
4. By lem-weil-pbc-serre-criterion-normal and def-weil-pbc-serre-conditions-rk-sk, a
   nonregular stalk has dimension greater than one, hence exactly two by step 3.
5. A proper specialization of such a point would append a prime to an attained chain
   of length two, contradicting step 3. Thus all singular points are closed.
6. Apply lem-sc-noetherian-closed-points-finite to the closed singular locus. This also
   handles an empty singular locus.
7. A singular stalk is excellent by lem-exc-finite-type-localization-excellent. It is
   Noetherian, local and a normal domain by step 1. Each of its prime localizations is
   normal by lem-weil-pbc-localization-normal-domain.
8. Its completion is Noetherian by lem-weil-pbc-adic-completion-noetherian, local by
   lem-weil-pbc-local-completion-local-ring, and complete by
   lem-weil-pbc-adic-completion-mod-ideal, since the maximal ideal is finitely generated.
   Its dimension is two by lem-weil-pbc-completion-dimension.
9. Excellence includes the G-ring property. By lem-weil-pbc-g-ring-completion-regular,
   the completion map is flat with geometrically regular fibres. The trivial field
   extension makes these fibres regular, hence normal by lem-weil-pbc-regular-ring-normal.
   Apply lem-weil-pbc-flat-normal-fibres-noetherian-normal to obtain normality of the
   completion at every prime.
10. Localization at the maximal ideal of a local ring is an isomorphism: all denominators
    are already units. Thus the normal local completion itself is a normal domain. -/
theorem excellent_normal_surface_local_data
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hNormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hDim : topologicalKrullDim X = 2) :
    IsOpen {x : X | IsRegularLocalRing (X.presheaf.stalk x)} ∧
    {x : X | ¬ IsRegularLocalRing (X.presheaf.stalk x)}.Finite ∧
    ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
      IsClosed ({x} : Set X) ∧
      IsExcellent (X.presheaf.stalk x) ∧
      IsNoetherianRing (X.presheaf.stalk x) ∧
      IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x) ∧
      IsLocalRing (X.presheaf.stalk x) ∧
      ringKrullDim (X.presheaf.stalk x) = 2 ∧
      IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) ∧
      IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) ∧
      IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) ∧
      IsAdicComplete
        (IsLocalRing.maximalIdeal
          (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x)))
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)) ∧
      ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) = 2 := by
  sorry

end AlgebraicGeometry
