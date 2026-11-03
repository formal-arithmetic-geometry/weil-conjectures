/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization

/-!
# The proper direct image on `Dᵇc(-, ℚ̄_ℓ)` and coproducts

Two inputs on the derived direct image `Rf_*` of `ℓ`-adic pro-étale sheaves, in the
Bhatt–Scholze model of `Dᵇc(-, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`), used to lift the
adjunction `Rf_* ⊣ Rf^!` to Weil complexes:

- `ProEtale.isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar_of_isProper`:
  for a proper morphism `f` of schemes of finite type over an algebraically closed field `k` with
  `ringChar k ≠ ℓ`, `Rf_* : Dᵇc(Y, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` is a left adjoint (blueprint
  `lem-sfb-dc-proper-pushforward-left-adjoint-qlbar`);
- `AlgebraicGeometry.ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar`:
  for a quasi-compact quasi-separated morphism `f`, `Rf_*` commutes with `ℤ`-indexed coproducts
  of uniformly bounded below complexes.

Both are stated with `sorry`. The first is proved in the condensed model of `ℓ`-adic sheaves
(`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`);
what is missing is the transfer to the present model: no comparison of `boundedConstructibleAdic`
with the condensed `boundedConstructible` exists yet. The second is the continuity of
cohomology of a coherent topos in bounded below degrees (SGA 4 VI 5.1, Bhatt–Scholze); it is
known for abelian sheaves in degree `0`
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_rightDerived_lowerStar`), but its
extension to bounded below complexes of `ℚ̄_ℓ`-modules is missing.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {l : ℕ} [Fact l.Prime] {Y X : Scheme.{u}}

section Proper

variable {k : Type u} [Field k] [IsAlgClosed k] (s : X ⟶ Spec (.of k))
  [LocallyOfFiniteType s] [QuasiCompact s] (hk : ringChar k ≠ l)

/-- **The proper direct image on `Dᵇc(-, ℚ̄_ℓ)` is a left adjoint** (blueprint
`lem-sfb-dc-proper-pushforward-left-adjoint-qlbar`; SGA 4 XVIII 3.1.4, SGA 4½ *Th. finitude*):
for a proper morphism `f : Y ⟶ X`, with `X` quasi-compact and locally of finite type over an
algebraically closed field `k` with `ringChar k ≠ ℓ`, the direct image
`Rf_* : Dᵇc(Y, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` has a right adjoint `Rf^!`.

This is proved in the condensed model of `ℓ`-adic sheaves as
`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`;
it is stated here with `sorry` because the transfer to the present model of `ℓ`-adic sheaves
(sheaves of modules over the constant sheaf `ℚ̄_ℓ`) is missing: no comparison of
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic` with the condensed
`boundedConstructible` exists yet. -/
theorem ProEtale.isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar_of_isProper
    (f : Y ⟶ X) [IsProper f] :
    (ProEtale.boundedConstructibleAdicRightDerivedLowerStar (l := l) s hk f).IsLeftAdjoint :=
  sorry

end Proper

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
