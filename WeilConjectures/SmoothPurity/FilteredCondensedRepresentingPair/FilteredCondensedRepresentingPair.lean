/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.Pair.FilteredCondensedRepresentingPairData
import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.FilteredCondensedCanonicalComparisons
import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.FilteredCondensedCounitFiniteFormula
import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.FilteredCondensedCounitBijective

/-! # A step of filtered condensed representing-pair descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
attribute [local irreducible] CondensedRing.boundedConstructibleLowerShriekOfCompactification
  constructibleExtendScalars constructibleToPadicAlgCl
  constructibleToPadicAlgClCompIso
variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

end WeilConjectures.FilteredCondensedRepresentingPair
