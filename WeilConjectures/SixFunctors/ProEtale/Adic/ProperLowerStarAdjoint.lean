/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization

/-!
# The derived direct image of `ℓ`-adic sheaves and coproducts

For a quasi-compact quasi-separated morphism `f`, the derived direct image `Rf_*` of `ℓ`-adic
pro-étale sheaves commutes with `ℤ`-indexed coproducts of uniformly bounded below complexes
(`AlgebraicGeometry.ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar`).
This is used to lift the adjunction `Rf_* ⊣ Rf^!` to Weil complexes. It is the continuity of
cohomology of a coherent topos in bounded below degrees (SGA 4 VI 5.1, Bhatt–Scholze).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {l : ℕ} [Fact l.Prime] {Y X : Scheme.{u}}

/-- **The derived direct image commutes with bounded below coproducts** (SGA 4 VI 5.1;
Bhatt–Scholze, *The pro-étale topology for schemes*, the pro-étale topos of a qcqs scheme being
coherent): for a quasi-compact quasi-separated morphism `f : Y ⟶ X`, the derived direct image
`Rf_*` of `ℓ`-adic pro-étale sheaves preserves the coproduct of a `ℤ`-indexed family of
complexes which are uniformly bounded below.

It is stated here with `sorry`: the continuity of higher direct images is known for abelian
sheaves (`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_rightDerived_lowerStar`),
but its extension to uniformly bounded below complexes of sheaves of `ℚ̄_ℓ`-modules (through
the hypercohomology spectral sequence, or a way-out argument) is missing. -/
theorem ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (K : ℤ → DerivedCategory (ProEtale.AdicSheaf l Y))
    (a : ℤ) (hK : ∀ n, (K n).IsGE a) :
    PreservesColimit (Discrete.functor K) (ProEtale.adicLowerStar l f).rightDerivedFunctor :=
  sorry

end AlgebraicGeometry
