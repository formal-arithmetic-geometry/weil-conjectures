/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BoundedBelowCoproducts
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit

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

The first is stated with `sorry`. It is proved in the condensed model of `ℓ`-adic sheaves
(`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`);
what is missing is the transfer to the present model: no comparison of `boundedConstructibleAdic`
with the condensed `boundedConstructible` exists yet.

The second is the continuity of cohomology of a coherent topos in bounded below degrees
(SGA 4 VI 5.1, Bhatt–Scholze). The higher direct images `Rᵠf_*` of `ℓ`-adic sheaves commute with
direct sums
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_rightDerived_adicLowerStar`),
by the case of abelian sheaves
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_rightDerived_lowerStar`); this
extends to uniformly bounded below complexes by representing them by complexes of injectives
(`CategoryTheory.Functor.preservesColimit_discrete_rightDerivedFunctor_of_isGE_of_rightDerived`).
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

/-- The underlying abelian sheaf of `ℓ`-adic sheaves commutes with direct sums: the forgetful
functor from `ℚ̄_ℓ,X`-modules creates them, `ℚ̄_ℓ,X ⊗ -` commuting with colimits, and the
underlying abelian sheaf of sheaves of `ℚ̄_ℓ`-modules is a left adjoint. -/
instance ProEtale.AdicSheaf.preservesColimitsOfShape_discrete_toAb (X : Scheme.{u}) (B : Type) :
    PreservesColimitsOfShape (Discrete B) (ProEtale.AdicSheaf.toAb l X) := by
  have : PreservesColimitsOfSize.{0, 0} (ProEtale.weilCoefficientsForgetAb l X) :=
    preservesColimitsOfSize_shrink _
  have : PreservesColimitsOfSize.{0, 0}
      (MonoidalCategory.tensorLeft (ProEtale.adicConstantSheaf l X)) :=
    preservesColimitsOfSize_shrink _
  unfold ProEtale.AdicSheaf.toAb
  infer_instance

/-- **Higher direct images of `ℓ`-adic sheaves commute with direct sums**: for a quasi-compact
quasi-separated morphism `f`, the classical right derived functors `Rᵠf_*` of `ℓ`-adic sheaves
preserve coproducts. This follows from the case of abelian sheaves
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_rightDerived_lowerStar`), as
`(Rᵠf_* F)_ab ≅ Rᵠf_*(F_ab)` (`AlgebraicGeometry.ProEtale.rightDerivedAdicLowerStarToAbIso`)
and taking underlying abelian sheaves commutes with direct sums and reflects isomorphisms. -/
theorem ProEtale.preservesColimitsOfShape_discrete_rightDerived_adicLowerStar (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (B : Type) (q : ℕ) :
    PreservesColimitsOfShape (Discrete B) ((ProEtale.adicLowerStar l f).rightDerived q) := by
  have := ProEtale.preservesColimitsOfShape_discrete_rightDerived_lowerStar f B q
  have : PreservesColimitsOfShape (Discrete B)
      ((ProEtale.adicLowerStar l f).rightDerived q ⋙ ProEtale.AdicSheaf.toAb l X) :=
    preservesColimitsOfShape_of_natIso (ProEtale.rightDerivedAdicLowerStarToAbIso l f q).symm
  have := reflectsColimitsOfShape_of_reflectsIsomorphisms (J := Discrete B)
    (G := ProEtale.AdicSheaf.toAb l X)
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (ProEtale.AdicSheaf.toAb l X)

/-- **The derived direct image commutes with bounded below coproducts** (SGA 4 VI 5.1;
Bhatt–Scholze, *The pro-étale topology for schemes*, the pro-étale topos of a qcqs scheme being
coherent): for a quasi-compact quasi-separated morphism `f : Y ⟶ X`, the derived direct image
`Rf_*` of `ℓ`-adic pro-étale sheaves preserves the coproduct of a `ℤ`-indexed family of
complexes which are uniformly bounded below.

The higher direct images `Rᵠf_*` commute with direct sums
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_discrete_rightDerived_adicLowerStar`), so
this is an instance of
`CategoryTheory.Functor.preservesColimit_discrete_rightDerivedFunctor_of_isGE_of_rightDerived`:
the family is represented by complexes of injectives strictly concentrated in degrees `≥ a`,
whose coproduct is a bounded below complex of `f_*`-acyclic sheaves. -/
theorem ProEtale.preservesColimit_discrete_rightDerivedFunctor_adicLowerStar (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] (K : ℤ → DerivedCategory (ProEtale.AdicSheaf l Y))
    (a : ℤ) (hK : ∀ n, (K n).IsGE a) :
    PreservesColimit (Discrete.functor K) (ProEtale.adicLowerStar l f).rightDerivedFunctor :=
  (ProEtale.adicLowerStar l f).preservesColimit_discrete_rightDerivedFunctor_of_isGE_of_rightDerived
    (ProEtale.preservesColimitsOfShape_discrete_rightDerived_adicLowerStar f ℤ) K a hK

end AlgebraicGeometry
