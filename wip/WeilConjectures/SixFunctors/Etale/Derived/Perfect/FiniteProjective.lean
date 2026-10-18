/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect

/-!
# Internal hom with a finite projective module

A sheaf `P` of `Λ`-modules on the small étale site of `X` is a *finite projective
`Λ_X`-module* if, étale locally on `X`, it is a direct summand of a finite free module
`Λ_U^{⊕m}` (`AlgebraicGeometry.Etale.IsFiniteProjectiveSheaf`). Placed in degree `0` it is
perfect on the coefficient site, hence dualizable in `D(X_ét, Λ)`. Consequently the canonical
map `P^∨ ⊗ᴸ N ⟶ RHom(P, N)` of the tensor–internal-hom adjunction is an isomorphism for every
`N`, and the biduality map `P ⟶ P^∨∨` is an isomorphism (blueprint
`lem-pod-finite-projective-tensor-hom`).

## Implementation notes

The blueprint works on the small pro-étale site; as for
`AlgebraicGeometry.Etale.DerivedCategory.IsSitePerfect`, the statement is made here on the small
étale site of the étale model. The dual `P^∨` is the derived dual
`RHom(P, Λ_X) = AlgebraicGeometry.Etale.DerivedCategory.coefficientDual`, and the biduality map
is `AlgebraicGeometry.Etale.DerivedCategory.coefficientDualDoubleDual`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {Y : Scheme.{u}}

/-- For a dualizable `K` in `D(Y_ét)`, the canonical map `RHom(K, 𝟙) ⊗ᴸ N ⟶ RHom(K, N)` is an
isomorphism for every `N`: `RHom(K, 𝟙)` is then a left dual of `K`. -/
theorem DerivedCategory.isIso_ihomUnitTensorToIhom_of_isDualizableEtale
    {K : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : DerivedCategory.IsDualizableEtale K) (N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom K N) := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := Etale.DerivedCategory.nonempty_exactPairing_swap K Kᘁ
  exact MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K N

end General

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- A sheaf `P` of `Λ`-modules on `X_ét` is a *finite projective `Λ_X`-module* if there is an
étale cover `{uᵢ : Uᵢ ⟶ X}` such that each restriction `uᵢ^* P` is a direct summand (a retract)
of a finite free module, the constant sheaf `(Λ^m)_{Uᵢ}`. -/
def IsFiniteProjectiveSheaf (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀, ∃ m : ℕ,
    Nonempty (Retract ((𝒰.f i)^*[ModuleCat.{u + 1} Λ].obj P)
      ((constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin m → Λ))))

namespace IsFiniteProjectiveSheaf

variable {P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- A finite projective `Λ_X`-module placed in degree `0` is perfect on the coefficient site:
on each member `u` of a trivializing cover, `Lu^* P ≅ u^* P` is the single complex on a
direct summand of `(Λ^m)_U`. -/
theorem isSitePerfect (hP : IsFiniteProjectiveSheaf P) :
    DerivedCategory.IsSitePerfect ((DerivedCategory.singleFunctor _ 0).obj P) := by
  obtain ⟨𝒰, h⟩ := hP
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨m, ⟨r⟩⟩ := h i
  let F := (𝒰.f i)^*[ModuleCat.{u + 1} Λ].obj P
  refine ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F, 0, 0, inferInstance,
    inferInstance, fun n ↦ ?_, ⟨(singleFunctorCompLeftDerivedUpperStarIso _ (𝒰.f i)).app P ≪≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).app F⟩⟩
  by_cases hn : n = 0
  · subst hn
    exact ⟨m, ⟨(Retract.ofIso (HomologicalComplex.singleObjXSelf _ 0 F)).trans r⟩⟩
  · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn
    exact ⟨0, ⟨{ i := 0, r := 0, retract := hz.eq_of_src _ _ }⟩⟩

/-- A finite projective `Λ_X`-module placed in degree `0` is dualizable in `D(X_ét, Λ)`. -/
theorem isDualizable (hP : IsFiniteProjectiveSheaf P) :
    DerivedCategory.IsDualizableEtale ((DerivedCategory.singleFunctor _ 0).obj P) :=
  hP.isSitePerfect.isDualizable

/-- Blueprint `lem-pod-finite-projective-tensor-hom`: Internal Hom with a finite projective
module.

For a finite projective `Λ_X`-module `P` and every `N ∈ D(X_ét, Λ)` (in particular every
`N ∈ Dctf(X, Λ)`), the canonical map `P^∨ ⊗ᴸ N ⟶ RHom(P, N)` of the tensor–internal-hom
adjunction (`CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`, natural in `P` and `N`) is an
isomorphism, `P^∨ = RHom(P, Λ_X)` being the coefficient dual. -/
theorem isIso_ihomUnitTensorToIhom (hP : IsFiniteProjectiveSheaf P)
    (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom ((DerivedCategory.singleFunctor _ 0).obj P) N) :=
  DerivedCategory.isIso_ihomUnitTensorToIhom_of_isDualizableEtale hP.isDualizable N

/-- Blueprint `lem-pod-finite-projective-tensor-hom`: Internal Hom with a finite projective
module.

For a finite projective `Λ_X`-module `P`, the biduality map `P ⟶ P^∨∨` is an isomorphism
(`AlgebraicGeometry.Etale.DerivedCategory.coefficientDualDoubleDual`). -/
theorem isIso_coefficientDualDoubleDual_app (hP : IsFiniteProjectiveSheaf P) :
    IsIso ((DerivedCategory.coefficientDualDoubleDual (ModuleCat.{u + 1} Λ) X).app
      ((DerivedCategory.singleFunctor _ 0).obj P)) :=
  DerivedCategory.isIso_coefficientDualDoubleDual_app hP.isDualizable

end IsFiniteProjectiveSheaf

end Etale

end AlgebraicGeometry
