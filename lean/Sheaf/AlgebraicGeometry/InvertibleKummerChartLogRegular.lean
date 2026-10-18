/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.AlgebraicGeometry.LogRegularCompletedChart
import Sheaf.RingTheory.FormalMonoidRingDimension
import Sheaf.RingTheory.LocalCompletionQuotient
import Sheaf.RingTheory.CompletionRegularLocal
import Sheaf.RingTheory.CompletionDimension
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.RingTheory.StrictHenselizationRegular
import Sheaf.RingTheory.StrictHenselizationDimension

/-!
# Log regularity for invertible Kummer charts

Source: Illusie--Laszlo--Orgogozo, Exposé VI 1.8, 2.2--2.3
(blueprint: lem-per-invertible-kummer-chart-log-regular).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An invertible Kummer chart over a log regular fs target preserves log regularity.
Source: Illusie--Laszlo--Orgogozo, Exposé VI 1.8, 2.2--2.3
(blueprint: lem-per-invertible-kummer-chart-log-regular).

For every source point, the compatible fs chart has injective monoid and group maps,
every target monomial has a positive power in the image, and its finite group cokernel
is killed by an integer which is a unit on the target chart neighbourhood. The canonical
scheme comparison is etale. The conclusion is precisely log regularity of the source;
no regularity of its underlying scheme and no torsion-freeness conclusion is asserted.

Proof plan:
1. Fix a geometric source point and its target chart point. Put `A` equal to the
   target strict local ring and `C = A ⊗[ℤ[P]] ℤ[Q]`. Localize `C` at the chart
   comparison point to obtain `B`. Strict henselization, finite-type algebra, and
   localization Noetherianity give Noetherianity of these local rings.
2. Apply `lem-trf-ind-etale-strict-local-invariance` to the strict-local structural
   base change and the etale comparison. This identifies the source strict local
   ring with the strict henselization of `B`, preserving chart monomials.
3. Let `G` and `F` be the faces of monomials becoming units in `A` and `B`.
   `lem-trf-fs-face-sharpening` identifies their sharpenings with the two
   characteristic monoids. The sharp-chart and completed-chart theorems give the
   target completed monoid-ring presentation. Retain the unit character relating
   the original chart to its sharp chart; do not assume the original chart sharp.
4. Apply `lem-per-completed-invertible-kummer-monoid-extension` with the given
   injectivity, Kummer, and invertible-annihilator hypotheses. It gives a pair
   isomorphism of the completed source ring and its monomial ideal with a formal
   monoid ring over a complete regular coefficient ring, or its mixed-characteristic
   parameter quotient. The stratum ideal is preserved in both cases.
5. `lem-trf-formal-monoid-ring-dimension` gives regularity of the completed stratum
   quotient and dimension equal to the stratum dimension plus characteristic rank.
   In mixed characteristic the parameter reduces both ring and stratum dimensions
   by one, leaving the same rank difference.
6. `lem-weil-pbc-local-completion-quotient`, completion regularity and dimension,
   closed-immersion strict localization, and strict-henselization regularity and
   dimension descend these two conditions to the source geometric stalk. They are
   exactly log regularity at that point. Every point is covered, including the
   vacuous case of an empty source. This is ILO VI 2.2--2.3.
-/
theorem invertibleKummerChart_logRegular
    (X Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y)
    (hY : Y.IsLogRegular)
    (hcharts : ∀ x : X.scheme, ∃ c : FSLogChart f,
      x ∈ Set.range c.V.hom ∧
        Function.Injective c.g ∧
        Function.Injective c.groupMap ∧
        Finite c.cokernel ∧
        (∀ q : c.Q, ∃ n : ℕ, 0 < n ∧ ∃ p : c.P, c.g p = q ^ n) ∧
        (∃ n : ℕ, 0 < n ∧
          (∀ z : c.cokernel, z ^ n = 1) ∧
          (∀ y : c.W.left, IsUnit ((n : ℕ) : c.W.left.presheaf.stalk y))) ∧
        Etale c.comparison) :
    X.IsLogRegular := by
  sorry

end AlgebraicGeometry
