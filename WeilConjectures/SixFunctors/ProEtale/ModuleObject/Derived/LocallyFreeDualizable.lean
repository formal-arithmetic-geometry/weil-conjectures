/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-!

# Locally free sheaves are dualizable in the bounded constructible derived category

Let `Λ` be an `ℓ`-adic coefficient ring (`IsEllAdicFinitenessCoefficient ℓ Λ`, for instance
`ℚ̲̄_ℓ`) and `Z` a separated scheme of finite type over a field `k` of characteristic different
from `ℓ`. A locally free module object `M` over `Λ_Z` (`ProEtale.IsLocallyFree`), placed in
degree `0`, is a dualizable object of `Dᵇc(Z)⟦Λ⟧`
(`ProEtale.CondensedRing.isDualizable_singleFunctor_of_isLocallyFree_of_isEllAdic`, and
`ProEtale.CondensedRing.isDualizable_singleFunctor_of_isLocallyFree` for `ℚ̲̄_ℓ`).

## The argument

The module object `M` is dualizable in `Mod_{Λ_Z}` (`ProEtale.IsLocallyFree.isDualizable`), so
the complex `M[0]` is a bounded complex of dualizable objects, hence dualizable in the derived
category `D(Mod_{Λ_Z})` (`DerivedCategory.isDualizable_Q_obj`). Its dual `RHom(M[0], Λ_Z)` is
again bounded constructible, `Dᵇc(Z)⟦Λ⟧` being a full monoidal closed subcategory of
`D(Mod_{Λ_Z})` (`ProEtale.CondensedRing.isMonoidal_boundedConstructible`,
`ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`), so `M[0]` is dualizable in
`Dᵇc(Z)⟦Λ⟧` (`ObjectProperty.isDualizable_of_isDualizable_obj`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]

/-- **A locally free sheaf in degree `0` is dualizable in `Dᵇc(Z)⟦Λ⟧`**, for an `ℓ`-adic
coefficient ring `Λ`: a locally free module object over `Λ_Z` is dualizable in `Mod_{Λ_Z}`, hence
so is the complex `M[0]` in the derived category, and its dual is bounded constructible. -/
theorem isDualizable_singleFunctor_of_isLocallyFree_of_isEllAdic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    [IsEllAdicFinitenessCoefficient ℓ Λ] (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1}) (condensedRingObj Λ Z.left))
    (hM : IsLocallyFree (condensedRingObj Λ Z.left) M) :
    IsDualizable (C := Dᵇc(Z.left)⟦Λ⟧)
      ⟨(DerivedCategory.singleFunctor _ 0).obj M,
        boundedConstructible_singleFunctor_obj _ Z.left 0 M hM.isConstructibleModuleObject⟩ := by
  let := DerivedCategory.braidedCategory'
    (C := Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1}) (condensedRingObj Λ Z.left))
  refine ObjectProperty.isDualizable_of_isDualizable_obj _ _ ?_
  refine DerivedCategory.isDualizable_Q_obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) 0 0 fun n ↦ ?_
  by_cases hn : n = 0
  · subst hn
    exact IsDualizable.of_iso (HomologicalComplex.singleObjXSelf _ _ M).symm hM.isDualizable
  · exact IsZero.isDualizable (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

variable [Fact ℓ.Prime] [Fact (ringChar k).Prime]

omit [Fact (ringChar k).Prime] in
/-- **A lisse `ℚ̄_ℓ`-sheaf in degree `0` is dualizable in `Dᵇc(Z)⟦ℚ̲̄_ℓ⟧`**: a locally free
module object over `ℚ̲̄_ℓ,Z`, placed in degree `0`, is a dualizable bounded constructible
complex. -/
theorem isDualizable_singleFunctor_of_isLocallyFree (Z : Over (Spec (.of k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left))
    (hM : IsLocallyFree (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left) M) :
    IsDualizable (C := Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
      ⟨(DerivedCategory.singleFunctor _ 0).obj M,
        boundedConstructible_singleFunctor_obj _ Z.left 0 M hM.isConstructibleModuleObject⟩ :=
  isDualizable_singleFunctor_of_isLocallyFree_of_isEllAdic ℓ _ Z M hM

end AlgebraicGeometry.ProEtale.CondensedRing
