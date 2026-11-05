/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleRightDerivedLowerStar

/-!
# Extension of scalars `ℚ̄_ℓ ⊗_{ℤ_ℓ} -` and higher direct images

For a morphism of schemes `f : X ⟶ Y`, restriction of scalars from `ℓ`-adic sheaves to
`ℤ_ℓ`-modules commutes with the pushforwards
(`AlgebraicGeometry.ProEtale.adicLowerStarRestrictPadicIntPushforwardIso`), and its mate is the
canonical comparison
```
ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)
```
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsPushforwardComparison`). We show that the
induced base change morphism of derived pushforwards
`ℚ̄_ℓ ⊗ Rᵠf_* M ⟶ Rᵠf_* (ℚ̄_ℓ ⊗ M)` is an isomorphism as soon as
1. extension of scalars `ℚ̄_ℓ ⊗ -` is exact on `X` and on `Y`;
2. the comparison `ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)` is an isomorphism;
3. for every injective `ℤ_ℓ,X`-module `I`, the abelian sheaf underlying `ℚ̄_ℓ ⊗ I` is
   `f_*`-acyclic

(`isIso_rightDerivedFunctorPlusBaseChange_adicSheafExtendScalarsPushforwardComparison`),
which gives an isomorphism of `ℓ`-adic sheaves
`ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0]) ≅ Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])`
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsHomologyRightDerivedIso`) and hence the
lisse-ness of `Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])` when `ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0])` is lisse
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_of_baseChange`).

Mathematically, all three conditions hold for `f` quasi-compact and quasi-separated, since
`ℚ̄_ℓ,X` is a filtered colimit of free `ℤ_ℓ,X`-modules of finite rank and `Rᵠf_*` commutes with
filtered colimits
(`WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

section BaseChange

variable [PreservesFiniteLimits (adicSheafExtendScalars X l)]
  [PreservesFiniteLimits (adicSheafExtendScalars Y l)]

end BaseChange

end AlgebraicGeometry.ProEtale
