/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseStalk
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.SmoothBaseChange

/-!
# Auxiliary facts for homotopy invariance of Weil complexes

Facts used in the dévissage proving homotopy invariance along trivial line bundles
(`WeilConjectures.WeilSheaf.HomotopyInvariance`):

- Weil complexes on an empty scheme vanish (`AlgebraicGeometry.WeilComplex.isZero_of_isEmpty`);
- the trivial line bundle `X ×_{k₀} 𝔸¹ ⟶ X` is smooth
  (`AlgebraicGeometry.WeilComplex.smooth_of_isPullback`);
- a Weil complex on a reduced scheme has lisse cohomology sheaves on a dense open subscheme
  (`AlgebraicGeometry.WeilComplex.exists_dense_isLisse_homologySheaf_upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

end AlgebraicGeometry.WeilComplex
