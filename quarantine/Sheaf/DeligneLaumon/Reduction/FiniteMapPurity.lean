/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q47
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.WeilSheaf.LowerStar
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.Paper.SfDerivedDirectImage

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.AdicPunctualWeights
import Sheaf.Paper.A1FiniteEtaleWeilFibreComparison
import Sheaf.Paper.A1FiniteWeilSectionsDecomposition
/-! # Purity under finite étale pushforward

Source: the blueprint of the Weil conjectures, chapter `sec-deligne-laumon-a1`,
unit `sk-thm-dl-a1-upper`, node `lem-a1-finite-map-purity`
(blueprint: lem-a1-finite-map-purity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- If `π` is finite étale and `F` is punctually `ι`-pure of weight `w`, then
`π₀ * F` is punctually `ι`-pure of weight `w`.

The proof follows the finite-fibre decomposition in the blueprint: the direct-image stalk
splits into finite Frobenius blocks, and an eigenvalue on a block has a positive power equal
to a local Frobenius eigenvalue of `F`; residue cardinalities satisfy the corresponding
power relation. The source is the first paragraph and displayed norm identity of
`literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/
lem-a1-finite-map-purity.proof.md`, using nodes
`lem-a1-finite-etale-weil-fibre-comparison` and
`lem-a1-finite-weil-sections-decomposition`.
For a block of length `e`, an eigenvector with eigenvalue `λ` has a nonzero stalk
component with local eigenvalue `α = λ^e`. Purity on the source gives
`|ι α| = q_x^(w/2)`, while `q_x = q_y^e` gives
`|ι λ|^e = (q_y^(w/2))^e`. Both sides are nonnegative and `e` is positive,
so taking the positive `e`-th root gives the required target weight. No diagonalization
is needed. An empty fibre or a zero stalk has no eigenvalues, so the claim is vacuous.
(blueprint: lem-a1-finite-map-purity).
-/
theorem isPunctuallyPureOfWeight_lowerStar_of_isFiniteEtale
    (ι : PadicAlgCl l ≃+* ℂ) {w : ℝ} {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of k₀))]
    [IsFinite π] [Etale π]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l X}
    (h : F.IsPunctuallyPureOfWeight ι.toRingHom w) :
    ((lowerStar π).obj F).IsPunctuallyPureOfWeight ι.toRingHom w := by
  sorry

end AlgebraicGeometry.WeilSheaf
