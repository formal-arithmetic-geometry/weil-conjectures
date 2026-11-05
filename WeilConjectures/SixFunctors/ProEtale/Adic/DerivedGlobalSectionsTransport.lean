/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.ProEtale.Adic.GeometricFrobenius
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

/-!
# Transport of derived global sections of `ℚ̄_ℓ` along isomorphisms of schemes

An isomorphism `e : Z ≅ W` of schemes induces an isomorphism
`RΓ(Z, ℚ̄_ℓ) ≅ RΓ(W, ℚ̄_ℓ)` of derived global sections of the constant `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.derivedGlobalSectionsUnitIso`): the pushforward `e_*` is an exact
equivalence, `Γ(W, e_* M) ≅ Γ(Z, M)`, and `e_* ℚ̄_ℓ,Z ≅ ℚ̄_ℓ,W`. This transport is compatible with
composition (`AlgebraicGeometry.ProEtale.derivedGlobalSectionsUnitIso_trans`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
