/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.ClosedOpenImmersion
public import Submission.WeilConjectures.WeilSheaf.Cohomology
public import Submission.WeilConjectures.WeilSheaf.LowerStarComp
public import Submission.WeilConjectures.WeilSheaf.OpenImmersion
public import Submission.WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek
public import Submission.WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Compactly supported and ordinary cohomology of a proper scheme

For a proper `k₀`-scheme `a : X ⟶ Spec k₀` the direct image with compact support
`Ra_! = Rg_* ∘ i_!`, for the chosen compactification `X ⟶[i] Z ⟶[g] Spec k₀`, is the derived
direct image `Ra_*`: the open immersion `i` is then also closed, so that `i_! ≅ i_*`, and
`Rg_* ∘ i_* ≅ R(i ≫ g)_*`. Hence the compactly supported cohomology of a Weil complex on `X`
is its ordinary cohomology, Frobenius-equivariantly.

## Main statements

- `AlgebraicGeometry.WeilComplex.derivedLowerShriekObjIsoOfIsProper`: `Ra_! K ≅ Ra_* K` for `X`
  proper.

This module only imports its parts, so that `import`s of
`WeilConjectures.WeilSheaf.ProperCohomology` keep working:

- `WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek`
- `WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion`
-/
