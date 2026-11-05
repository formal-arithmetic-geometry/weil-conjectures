/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationCoherence
public import WeilConjectures.WeilSheaf.Native.Projection.UncurriedComparison
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionForgetIsoTransport
public import WeilConjectures.WeilSheaf.Native.Projection.ProperProjectionForgetFormal
import WeilConjectures.Tactic.ExactModProofs

/-! # The proper projection square before restriction to bounded complexes -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : X ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

local notation "gb" => Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))
local notation "Λ" => Profinite.padicAlgClRingObj l

/-- The native right-adjoint projection map on all derived objects. -/
def nativeProperProjectionNatTrans :=
  Functor.uncurryRightProjection
    ((derivedUpperStarLowerStarAdjunction k₀ l g).rightAdjointProjectionMap
      (nativeCurriedPullTensor k₀ l g))

/-- The canonical proper pushforward comparison as natural-isomorphism data. -/
def nativeProperForgetIso :=
  asIso (mateEquiv (derivedUpperStarLowerStarAdjunction k₀ l g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ gb)
    (derivedCondensedRealizationUpperStarIso k₀ l g).hom).natTrans

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The right-adjoint projection map is compatible with the canonical realization square. -/
theorem nativeProperProjection_forgetSquare :
    ProjectionForgetSquare (nativeProperForgetIso k₀ l g)
      (derivedCondensedRealizationUpperStarIso k₀ l g).symm
      (condensedRealizationTensor k₀ l X) (condensedRealizationTensor k₀ l Y)
      (nativeProperProjectionNatTrans k₀ l g)
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ gb).uncurriedProjectionMorphismNatTrans := by
  exact Adjunction.projectionForgetSquare_of_comparisonCompatible
    (derivedUpperStarLowerStarAdjunction k₀ l g)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ gb)
    (derivedCondensedRealizationUpperStarIso k₀ l g) (nativeCurriedPullTensor k₀ l g)
    (condensedRealizationTensor k₀ l X) (condensedRealizationTensor k₀ l Y)
    (by exact_mod_proofs comparisonCompatible_derivedCondensedRealization k₀ l g)

end AlgebraicGeometry.ProEtaleWeilSheaf
