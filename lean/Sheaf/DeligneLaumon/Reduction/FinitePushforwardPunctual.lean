/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.WeilSheaf.LowerStar
import Sheaf.Paper.AdicPunctualWeights
import Sheaf.Paper.ZlFiniteAdicDirectImage
import Sheaf.Paper.A1FiniteWeilSectionsDecomposition

/-! # Finite pushforward preserves punctual upper bounds and purity

Source: the blueprint of the Weil conjectures, chapter `sec-deligne-laumon-general`,
unit `sk-l-dl-general-quasifinite`, node `lem-zl-finite-pushforward-punctual`
(blueprint: lem-zl-finite-pushforward-punctual).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.WeilSheaf

/-- A finite pushforward preserves punctual upper weight bounds and punctual purity.

The source statement is the finite-pushforward lemma in the general quasi-finite argument:
base change to the algebraic closure, use the finite geometric-stalk direct-sum formula and
its Frobenius equivariance, decompose the finite fibre into Frobenius cycles, and compare an
eigenvalue on a cycle of length `e` with the `e`-th power of the local eigenvalue. The residue
cardinalities satisfy `q_x = q_y ^ e`, so taking the nonnegative `e`-th root preserves both the
upper-bound inequality and the equality defining purity. The two implications below are
independent; zero fibres and zero stalks are vacuous because they have no eigenvalues.
(blueprint: lem-zl-finite-pushforward-punctual).
-/
theorem hasWeightsAtMost_and_isPunctuallyPureOfWeight_lowerStar_of_isFinite
    {k₀ : Type u} [Field k₀] [Finite k₀]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (ι : PadicAlgCl l ≃+* ℂ) {w : ℝ} {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsFinite f] {F : WeilSheaf k₀ l X} :
    (F.HasWeightsAtMost ι.toRingHom w →
      ((lowerStar f).obj F).HasWeightsAtMost ι.toRingHom w) ∧
    (F.IsPunctuallyPureOfWeight ι.toRingHom w →
      ((lowerStar f).obj F).IsPunctuallyPureOfWeight ι.toRingHom w) := by
  sorry

end AlgebraicGeometry.WeilSheaf
