/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
import WeilConjectures.WeilSheaf.Category
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.FiniteMittagLeffler
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.SfWeilSheafComplex

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Positive cohomology sheaves of compactly supported direct image from a finite scheme vanish.

Source: blueprint sec-deligne-laumon-a1/sk-i-dl-a1-local/
lem-a1-finite-boundary-cohomology.md, finite-discrete-space argument.
(blueprint: lem-a1-finite-boundary-cohomology-positive)

Proof: Write a for the structure morphism. Since a is finite, it is proper, so compactly
supported direct image agrees with ordinary derived direct image, independently of the chosen
compactification. After base change to the algebraic closure, the reduction of X is a finite
coproduct of spectra of the algebraically closed field: each local Artinian component has that
residue field. Nilpotent invariance of the etale and pro-etale sites removes the nilpotents.
For finite torsion coefficients, sections on this coproduct are a finite product of stalks,
which is exact; thus higher cohomology vanishes, including for the empty coproduct.
Choose a finite field of definition and a constructible integral lattice for G, and compute
adic direct image by the derived limit of its finite reductions. Their degree-zero cohomology
groups are finite, so their tower is Mittag--Leffler and has zero first derived limit. The
Milnor exact sequence gives zero cohomology in every positive degree (degree one uses precisely
this Mittag--Leffler assertion). Rationalization and scalar extension to the algebraic closure
of the coefficient field are exact, so preserve vanishing. Forgetting the Weil structure
commutes with derived direct image and detects zero objects; consequently the corresponding
Weil cohomology sheaf is zero. This argument uses no stalk-weight assumption. -/
theorem isZero_homology_compactSupport_of_isFinite_of_pos
    [IsFinite (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {r : ℤ} (hr : 0 < r) :
    IsZero ((WeilComplex.homologySheaf r).obj
      ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj G))) := by
  sorry

end AlgebraicGeometry.WeilSheaf
