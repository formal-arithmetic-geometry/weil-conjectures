/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.LogInfinitesimalLifting
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.AlgebraicGeometry.Thickening
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.EtaleLfpAndFiniteType
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.HenselianLocalRootLifting
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import Mathlib.LinearAlgebra.FreeModule.PID
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Infinitesimal criterion for fs logarithmic smoothness and etaleness

Source: Kato, Logarithmic structures of Fontaine--Illusie, 3.1--3.5 and Remark 3.6,
printed pp.200--202; ILO X Proposition 1.2 and proof, printed pp.136--139
(blueprint: lem-sfb-fs-log-infinitesimal-criterion).

The left sides use the recorded compatible fs chart definitions. The right sides test
all fine log structures on arbitrary schemes in the same universe, without Noetherian
or saturation assumptions on those schemes. Strictness tests the prescribed associated
inverse-image log structure on geometric stalks, using its unit-pushout congruence.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- The two infinitesimal equivalences for locally Noetherian fs log schemes.
Source: Kato 3.1--3.5 and Remark 3.6; ILO X Proposition 1.2, pp.136--139
(blueprint: lem-sfb-fs-log-infinitesimal-criterion).

Proof plan (the twelve steps of the node):

1. `lem-sfb-chart-log-smooth-deformation-calculus` gives local finite presentation and
   etale-local existence for arbitrary fine strict square-zero tests of a smooth chart.
   A log-etale chart also satisfies the smooth chart conditions, using
   `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.
2. For etale charts, the same calculus identifies differences of lifts with `(D, δ)`.
   The finite invertible-order group cokernel kills `δ` on chart generators; it then
   kills `D` on monomials. Full faithfulness of etale restriction across a thickening
   (`sbc-lem-thickening-etale-site`) kills the remaining difference. Units and chart
   generators kill all of `δ`. The local lifts glue by
   `lem-weil-pbc-small-etale-representable-presheaf-sheaf` and the log sheaf condition,
   giving a unique global lift.
3. Conversely, `lem-sfb-lifting-log-differential-calculus` gives a local dlog basis.
   `lem-trf-fs-face-sharpening` makes the sharp characteristic group finite free.
   Split its quotient by units, and use `lem-trf-fine-log-stalk-chart-spreading` to
   spread a sharp base chart `Q` to a pointed etale neighbourhood.
4. The differential relations give a residue-field surjection onto the characteristic
   group modulo `Q`. The chosen generators define `L = ℤ^r ⊕ Qᵍᵖ` mapping to that
   group. By `lem-sbc-finitely-generated-abelian-group-structure`, its cokernel is
   finite and killed by some positive `n` invertible at the point.
5. `lem-weil-pbc-strict-henselization-local-structure`, together with
   `lemma-weil-pbc-affine-neighbourhood-cofinal`, identifies the stalk ring as strictly
   henselian. Apply `lem-weil-pbc-henselian-local-root-lifting` to `T^n - u`: units
   are `n`-divisible. `lem-sfb-divisible-unit-lattice-extension` now extends `L` to a
   finite free group `G` surjecting onto the characteristic group, with quotient
   killed by a power of `n`.
6. The inverse image `P` of the log monoid in `G` splits as the sharp characteristic
   monoid times the group kernel. The latter is finite free by
   `lem-weil-subgroup-finite-free-abelian-group-free`. Hence `P` is fs and its
   pushout with units is exactly the original log stalk.
7. Spread this prescribed chart by `lem-trf-fine-log-stalk-chart-spreading`. The map
   `Qᵍᵖ → G` is injective with finite invertible-order torsion cokernel. In the unique
   lifting case the differential calculus gives rank zero, hence finite whole cokernel.
8. Form the scheme fibre product of the two monoid spectra over the base, restricted
   to the open where `n` is invertible. The comparison is strict. A finite presentation
   over the base, supplied by `lem-weil-pbc-lfp-affine-opens-finite-presentation`,
   remains finite over this chart ring by adjoining its finitely many generators and
   their substitution relations. Use `lem-kun-etale-lfp` and
   `lem-sbc-locally-finite-presentation-composition` on the etale neighbourhoods;
   `lem-weil-pbc-finite-type-algebra-noetherian` makes the comparison target locally
   Noetherian.
9. Compute the target log differentials as the tensor product with `G/Qᵍᵖ`. Since
   the index of `L` is killed by a power of the unit `n`, the differential comparison
   is an isomorphism at the point and on a neighbourhood. The two calculus nodes
   supply finite local freeness.
10. `lem-sfb-fine-chart-logification-thickening` equips arbitrary affine square-zero
    tests over the comparison target with the fine chart log structures. Obtain a
    local log lift over the original base. Its discrepancy over the comparison target
    is a differential homomorphism. Transport it by the differential isomorphism and
    subtract it using the torsor action of `lem-sfb-lifting-log-differential-calculus`.
11. The corrected lift is unique: the same differential isomorphism kills differences.
    Strictness and the logification universal property put every candidate scheme
    lift under this argument. The representable-presheaf sheaf condition glues them.
12. Apply `lem-sfb-lfp-unique-infinitesimal-lifts-etale` to the strict comparison.
    `lem-weil-pbc-etale-composition-cancellation` composes it with the open where `n`
    is invertible. Its smoothness follows from
    `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`. These are precisely the two
    chart conditions of `def-per-fs-log-smooth-etale`, giving both converses.
-/
theorem EtaleLogHom.infinitesimal_criterion {X Y : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) :
    (f.IsLogSmooth ↔ LocallyOfFinitePresentation f.base ∧
      f.toLogMap.HasEtaleLocalInfinitesimalLifts) ∧
    (f.IsLogEtale ↔ LocallyOfFinitePresentation f.base ∧
      f.toLogMap.HasUniqueInfinitesimalLifts) := by
  sorry

end AlgebraicGeometry
