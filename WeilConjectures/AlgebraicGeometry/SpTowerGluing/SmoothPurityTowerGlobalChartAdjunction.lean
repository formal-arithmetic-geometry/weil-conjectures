/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Data
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.Compactification.Triangle
import WeilConjectures.Compactification.CommonRefinement
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Algebra.Homology.SmoothPurity.InvertibleTensorScalarExtensionDefinitionsSupplement
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Data
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Global chart adjunction for smooth coefficient towers

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gluing.proof.md, paragraphs Local pairs, Gluing, Uniformity,
Uniqueness and functoriality (blueprint: lem-route-tower-global-chart-adjunction).

## Main statements

* `tower_global_chart_adjunction`: the global adjunction F_f ⊣ G on the full ordinary
  constructible finite-Tor tower categories, with a unique counit-preserving natural
  comparison j^*G ≅ e^*p_d^*(-)(d)[2d] on every etale coordinate chart and the shifted
  cohomological and Tor bounds.
* `tower_global_chart_adjunction_legacy`: the former statement (Charts witness), kept only
  for its importer `Sheaf.Paper.SmoothPurityTowerGluing` until that caller is re-split.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- The former global chart adjunction statement with the retired Charts witness, kept
under a new name for its importer only; its proof on main is archived in
coord/changes/M-lem-route-tower-global-chart-adjunction-proof-archive.md.
Source: blueprint det-sp-tower-gluing, Local pairs, Gluing, Uniformity, and
Uniqueness and functoriality (blueprint: lem-route-tower-global-chart-adjunction).

Proof (former route, see the archive): obtain the fixed calculus, the coordinate
adjunction and its chart family, the global representing pairs, assemble the adjunction
from them, and collect the chart comparisons into Charts. -/
theorem tower_global_chart_adjunction_legacy
    (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hne : pchar ≠ l)
    (X Y : Over (Spec (CommRingCat.of k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (hF : ∀ M : SpTowerCalculus.C l E b q X.left,
      spConstructibleTorTowers l E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F l E b o q
          (CondensedRing.compactificationOverField f)).obj M.obj)) :
    ∃ G : SpTowerCalculus.C l E b q Y.left ⥤ SpTowerCalculus.C l E b q X.left,
      ∃ adj : support l E b o q (CondensedRing.compactificationOverField f) hF ⊣ G,
        Nonempty (Charts l E b o q k X Y
          ⟨inferInstance, inferInstance, inferInstance⟩ f d
          (CondensedRing.compactificationOverField f) hF G adj) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerGluing
