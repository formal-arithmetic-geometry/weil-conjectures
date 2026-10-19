/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.VeryTameFSLogAction
public import Sheaf.AlgebraicGeometry.KummerLogMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import Sheaf.RingTheory.StrictHenselizationNoetherian
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.AlgebraicGeometry.InvertibleKummerChartLogRegular
import Sheaf.AlgebraicGeometry.LogRegularCompletedChart
import Sheaf.RingTheory.LogRegularSaturationNormality
import Sheaf.RingTheory.CompletionDimension
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.RingTheory.StrictHenselizationFaithfullyFlat
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.FiniteQuotientStrictLocalInvariants
import Sheaf.AlgebraicGeometry.TameAdmissibleSchemeQuotient
import Sheaf.AlgebraicGeometry.VeryTameEquivariantSharpChart
import Sheaf.AlgebraicGeometry.VeryTameLocalKummerQuotient

/-!
# Very tame quotient and its Kummer charts

Source: ILO, Exposé VI 2.1--2.3, Theorem 3.2, Proposition 3.5 and proof 3.7,
printed pp.71--76 (blueprint: lem-per-very-tame-log-quotient).

The quotient log structure is the existing invariant-direct-image notion. Neither
the quotient scheme nor its log structure is supplied as an extra hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A very tame admissible, generically free finite action has an fs log-regular
invariant quotient, finite surjective Kummer-étale projection, geometric orbit fibres,
strict local standard Kummer charts, and unique factorization of invariant log maps.

Source: ILO VI 2.1--2.3, Theorem 3.2, Proposition 3.5 and proof 3.7, pp.71--76
(blueprint: lem-per-very-tame-log-quotient).

Proof, following the ten DAG steps:
1. Apply lem-per-tame-admissible-scheme-quotient to the underlying action. This gives
   the Noetherian finite geometric categorical quotient and its invariant rings.
   Invariant log sections satisfy the log unit axiom: an invariant section mapping
   to a unit is a unit, whose inverse is invariant too.
2. Lem-per-finite-quotient-strict-local-invariants identifies the strict local rings
   as B = A^H and the quotient log stalk as M^H, for geometric inertia H; A is finite
   over B. Lem-sc-strict-henselization-noetherian gives Noetherianity. Log regularity
   of X gives a regular stratum A/I and its dimension formula.
3. Lem-per-very-tame-equivariant-sharp-chart gives the diagonal sharp fs chart Q.
   Lem-per-very-tame-local-kummer-quotient gives P = Q intersect ker(chi), an actual
   chart of the invariant log sheaf, finite index and B/J = A/I. Also nQ lies in P,
   where n is the inertia order, invertible in the residue field.
4. Lem-weil-pbc-finite-algebra-is-integral and
   lem-weil-pbc-integral-injective-dimension-equal give dim B = dim A. Finite index
   gives equal characteristic ranks. The regular stratum and dimension formula
   therefore give log regularity of Y, by def-trf-fs-log-blowup.
5. Lem-per-tame-diagonal-standard-closed-immersion gives the strict closed comparison
   from X to the standard cover, hence C = B tensor over Z[P] with Z[Q] surjects to A.
   Monomials with generator exponents less than n span C over B. Thus C is finite
   and Noetherian by lem-weil-pbc-finite-algebra-noetherian, and B embeds into C.
6. Lem-weil-pbc-finite-over-henselian-local-product and the nilpotence of nonzero
   monomials in the closed fibre show C is strictly local with the same residue
   field. Sharp saturation makes Qgp torsion free, so nonzero monomials really
   have positive powers in the base nonunit ideal. Apply
   lem-per-invertible-kummer-chart-log-regular to the standard cover over the log
   regular strict local base; lem-trf-ind-etale-strict-local-invariance transports
   the base log-regular conditions to every geometric point of its strict localization.
7. Lem-trf-log-regular-completed-chart and lem-trf-log-regular-saturation-normality
   make the completed strict local ring C a domain in either characteristic.
   Lem-weil-pbc-local-completion-faithfully-flat and
   lem-weil-pbc-faithfully-flat-universally-injective embed C in its completion.
8. The integral dimension theorem gives dim C = dim B = dim A; these dimensions
   are finite by lem-weil-pbc-completion-dimension. A nonzero kernel of C -> A
   would let a maximal prime chain in A extend downwards by (0) in the domain C.
   Hence C -> A is an isomorphism, giving the strict local cartesian chart.
9. Lem-trf-closed-immersion-strict-localization-cartesian identifies the localized
   comparison ideal. Lem-sc-strict-henselization-faithfully-flat and faithful-flat
   injectivity kill that ideal at the ordinary local ring. Finitely many generators
   let one shrink to an open where it vanishes. The comparison is thus étale on
   pointed neighbourhoods. Its finite group cokernel is killed by n, has order
   dividing a power of n, and is invertible. Def-per-fs-log-smooth-etale gives log
   étaleness; the chart multiple condition gives Kummer characteristic maps.
10. The scheme categorical property uniquely descends an invariant map to S.
    Its log map lands in the invariant subsheaf by invariance. The inclusion of
    that subsheaf in q_*M is injective, giving uniqueness of the log factorization. -/
theorem exists_veryTame_logQuotient
    (X : FineSaturatedLogScheme.{u}) [IsNoetherian X.scheme]
    (G : Type v) [Group G] [Finite G] (a : FSLogGroupAction G X)
    (hadmissible : ∀ x : X.scheme, ∃ U : X.scheme.Opens,
      x ∈ U ∧ IsAffineOpen U ∧
        ∀ (g : G) (z : X.scheme), (a.baseAction g).hom z ∈ U ↔ z ∈ U)
    (hfree : a.IsGenericallyFree) (hregular : X.IsLogRegular) (hverytame : a.IsVeryTame) :
    ∃ (Y : FineSaturatedLogScheme.{u}) (q : EtaleLogHom X Y),
      IsNoetherian Y.scheme ∧ IsFinite q.base ∧ Surjective q.base ∧ a.IsQuotient q ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x z : Spec (.of Ω) ⟶ X.scheme),
        x ≫ q.base = z ≫ q.base ↔ ∃ g : G, x ≫ (a.baseAction g).hom = z) ∧
      Y.IsLogRegular ∧ q.IsLogEtale ∧ q.IsKummer ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ X.scheme), q.HasStrictLocalKummerChart t) ∧
      ∀ (S : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X S),
        (∀ g : G, (a.logMap g).CompEq f f) →
          ∃! r : EtaleLogHom Y S, q.CompEq r f := by
  sorry

end AlgebraicGeometry
