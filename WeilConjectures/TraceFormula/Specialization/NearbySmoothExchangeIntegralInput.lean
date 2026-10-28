/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.TraceFormula.Specialization.DeformationModel

/-!

# Integral smooth base change along affine spaces for the geometric generic fibre

For the inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic fibre of the deformation model
`𝒴 = 𝒟_I Y` and the projection `π : 𝔸ⁿ_𝒴 ⟶ 𝒴`, the base change map `Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` with
coefficients `𝒪_E` is invertible at `Lε^* K₀` for every bounded constructible `𝒪_E`-complex `K₀` on
`Y` (`ProEtale.CondensedRing.isIso_baseChangeMap_affineSpace_deformationModel_app_padicIntegers`).

## Sorried input

This is smooth base change with integral `ℓ`-adic coefficients along the qcqs morphism `j`, which
is not of finite type. Its first derived reduction is the base change map with coefficients `𝔽_E`
at `Lε^* (K₀ ⊗ᴸ 𝔽_E)`, which is invertible by smooth base change with finite coefficients
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_smooth_of_finite`), the reduction commuting with
`Rj_*` (`ProEtale.CondensedRing.isIso_derivedUpperStarExtendScalarsPushHom_residueField_app`). So
the mapping cone `C` of the base change map is a complex on which `ℓ` acts invertibly. What is
missing is the derived `ℓ`-completeness of the source `Lπ^* Rj_* Lε^* K₀` and of the target
`Rj'_* Lπ'^* Lε^* K₀` (a derived complete complex on which `ℓ` is invertible vanishes):
derived completeness is not available for module objects over `𝒪_{E,X}`
(see `ProEtale.CondensedRing.properDirectImage_baseChange_projectionFormula_padicIntegersRingObj`),
and the available derived Nakayama (`ProEtale.isIso_of_isIso_derivedReduction_map`) only covers
bounded constructible complexes, while `Rj_* Lε^* K₀` is not constructible. For the source,
completeness of `Lπ^* N` for a derived complete `N` is not formal either (the pullback along `π`
does not commute with derived limits in general).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Integral smooth base change along affine spaces for the geometric generic fibre** (blueprint
`sbc-thm-bounded-derived-smooth-base-change`, for `𝒪_E`-coefficients and the projection
`π : 𝔸ⁿ_𝒴 ⟶ 𝒴`): for the inclusion `j : 𝒴_Ω ⟶ 𝒴` of the geometric generic fibre of the deformation
model `𝒴 = 𝒟_I Y` and the cartesian square of `j` along `π`, the base change morphism
`Lπ^* Rj_* ⟶ Rj'_* Lπ'^*` with coefficients `𝒪_E` is invertible at `Lε^* K₀` for every bounded
constructible `𝒪_E`-complex `K₀` on `Y`. It is `sorry`ed, see the module docstring. -/
theorem isIso_baseChangeMap_affineSpace_deformationModel_app_padicIntegers
    {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (I : Y.left.IdealSheafData) (n : ℕ) (E : FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y.left))}
    (hK₀ : boundedConstructible _ K₀) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E.1)
      (IsPullback.of_hasPullback (deformationModel Y I k').j
        (𝔸(ULift.{u} (Fin n); (deformationModel Y I k').total) ↘
          (deformationModel Y I k').total)).toCommSq).app
      ((L(((deformationModel Y I k').ε)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).obj K₀)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
