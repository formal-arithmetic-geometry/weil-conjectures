/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCounitIsIso
public import WeilConjectures.CategoryTheory.Triangulated.AdjunctionUnitLocal
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionClosedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionOpenLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReduction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.LowerStar

/-!

# Reduction modulo `ℓⁿ` read on the étale site commutes with `Rd^!` for closed immersions

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`, `n : ℕ`, and write
`red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small étale
site (`AlgebraicGeometry.ProEtale.CondensedRing.etaleReduction`). For a closed immersion
`d : Z ⟶ Y` of separated `k`-schemes of finite type and *any* isomorphism
`γ : Rd_! ⋙ red_Y ≅ red_Z ⋙ Rd_!`, this file proves that the transpose
`β : Rd^! ⋙ red_Z ⟶ red_Y ⋙ Rd^!` of `γ⁻¹` under the adjunctions `Rd_! ⊣ Rd^!` is an isomorphism
(`ProEtale.CondensedRing.isIso_mateEquiv_etaleReduction_of_isClosedImmersion`). This is the second
half of `ProEtale.CondensedRing.exists_etaleReductionLowerShriekIso`.

## Strategy

At `K`, the mate `β_K` is the unit of the étale adjunction `Rd_! ⊣ Rd^!`, then `Rd^!` of `γ⁻¹`,
then `Rd^! red_Y (ε_K)`, for `ε` the counit of the condensed adjunction `Rd_! ⊣ Rd^!`
(`CategoryTheory.isIso_mateEquiv_app_of_isIso_map_counit`). The étale unit is invertible, `Rd_!`
being fully faithful (`Etale.isIso_rightDerivedUpperShriekAdjunction_unit_app`), so `γ` drops out
and it remains to see that `Rd^! red_Y (ε_K)` is an isomorphism.

1. On `Dᵇc(Y)⟦𝒪_E⟧`, the counit `ε_K` and the unit `K ⟶ Rj_* j^* K` of the open complement
   `j : U ⟶ Y` of `d` extend to a distinguished triangle (the supported localization triangle,
   `ProEtale.CondensedRing.exists_distTriang_boundedConstructibleUpperShriekAdjunction_counit`),
   by the formal recollement argument `CategoryTheory.Pretriangulated.Recollement`: `Rd_! ≅ Rd_*`
   is fully faithful, `j^* Rd_* = 0`, and complexes killed by `j^*` come from `Z` by open–closed
   detection.
2. The reduction modulo `ℓⁿ` preserves the `j`-local objects `Rj_* L`
   (`isIso_derivedUpperStarLowerStarAdjunction_unit_app_integersModPowReduction`),
   and the finite-coefficient comparison `Φ` and `Rν_*` commute with `Rj_*`
   (`ProEtale.finiteCoefficientDerivedLowerStarIso`,
   `ProEtale.rightDerivedLowerStarCompComparisonLowerStarIso`); so `red_Y (Rj_* j^* K)` is an
   étale `Rj_* C`, which receives no maps from the shifts of `Rd_! B`
   (`Etale.subsingleton_hom_shift_rightDerivedLowerShriek_rightDerivedLowerStar`).
3. Hence composition with `red_Y (ε_K)` is bijective on morphisms out of `Rd_! B`, and
   `Rd^! red_Y (ε_K)` is an isomorphism by the Yoneda lemma along `Rd_! ⊣ Rd^!`
   (`CategoryTheory.Adjunction.isIso_map_of_bijective_comp`).

## Main results

- `ProEtale.CondensedRing.exists_distTriang_boundedConstructibleUpperShriekAdjunction_counit`: the
  supported localization triangle `Rd_! Rd^! K ⟶ K ⟶ Rj_* j^* K ⟶` on bounded constructible
  `𝒪_E`-complexes, for a closed immersion `d` with open complement `j`.
- `ProEtale.CondensedRing.isIso_rightDerivedUpperShriek_map_etaleReduction_map_counit`: `Rd^!`
  inverts the reduction of the counit of `Rd_! ⊣ Rd^!`.
- `ProEtale.CondensedRing.isIso_mateEquiv_etaleReduction_of_isClosedImmersion`: the transpose of
  any isomorphism `Rd_! ⋙ red_Y ≅ red_Z ⋙ Rd_!` is an isomorphism.

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-! ### The supported localization triangle on bounded constructible `𝒪_E`-complexes -/

section Triangle

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

end Triangle

/-! ### The reduction of `j`-local objects, read on the étale site -/

section Etale

section Comparison

variable (X : Scheme.{u}) (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T]

/-- The derived finite-coefficient comparison commutes with the shifts, being `D(Φ)` for the
exact equivalence `Φ = finiteCoefficientModEquivalence`. -/
noncomputable instance commShift_finiteCoefficientDerivedEquivalence_functor :
    (finiteCoefficientDerivedEquivalence X T).functor.CommShift ℤ :=
  inferInstanceAs (D((finiteCoefficientModEquivalence X T).functor).CommShift ℤ)

/-- The derived finite-coefficient comparison is triangulated, being `D(Φ)` for the exact
equivalence `Φ = finiteCoefficientModEquivalence`. -/
instance isTriangulated_finiteCoefficientDerivedEquivalence_functor :
    (finiteCoefficientDerivedEquivalence X T).functor.IsTriangulated :=
  inferInstanceAs (D((finiteCoefficientModEquivalence X T).functor).IsTriangulated)

end Comparison

/-- The reduction modulo `ℓⁿ` read on the small étale site, on the whole derived category of
`𝒪_{E,X}`-modules: `N ↦ Rν_* Φ(N ⊗ᴸ_{𝒪_E} 𝒪_E ⧸ ℓⁿ)`. On bounded constructible complexes it is
`etaleReduction` (`etaleReductionIsoDerivedEtaleReduction`). -/
noncomputable abbrev derivedEtaleReduction (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :=
  L(Mod.extendScalars (integersModPowReduction X ℓ E n)) ⋙
    (finiteCoefficientDerivedEquivalence X (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
      R(ν_*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])

/-- `etaleReduction` is the restriction of `derivedEtaleReduction` to bounded constructible
complexes. -/
noncomputable def etaleReductionIsoDerivedEtaleReduction (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    etaleReduction ℓ E n Y ≅ (boundedConstructible _).ι ⋙ derivedEtaleReduction ℓ E n Y.left :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedConstructibleIntegersModPowReductionCompatibility Y.left ℓ E n)
      _ ≪≫ Functor.associator _ _ _

/-- The étale reading of the reduction is triangulated. -/
instance isTriangulated_derivedEtaleReduction (X : Scheme.{u}) :
    (derivedEtaleReduction ℓ E n X).IsTriangulated := by
  infer_instance

end Etale

/-! ### The transpose of the compact-support comparison -/

section Main

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

end Main

end AlgebraicGeometry.ProEtale.CondensedRing
