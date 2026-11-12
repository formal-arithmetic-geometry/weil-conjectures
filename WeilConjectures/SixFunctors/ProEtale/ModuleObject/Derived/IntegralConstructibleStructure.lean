/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleModuleObjectsEssentiallySmall
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IndConstructibleHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Constructible
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.DerivedCategory.HomotopyColimit
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions

/-!
# Structure of integral constructible complexes

For a finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a noetherian scheme `X`, we collect the
structure of the bounded constructible complexes `Dᵇc(X, 𝒪_E)` of module objects over `𝒪_{E,X}`
and of the constructible sheaves `Cons(X, 𝒪_E)`
(`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_padicIntegersRingObj_structure`,
blueprint `lemma-structure-integral-constructible-complexes--1`):
`Dᵇc(X, 𝒪_E)` is a triangulated subcategory of bounded objects of `D(X_proét, 𝒪_E)`, stable
under the truncations; its objects in degree `0` are the constructible sheaves, which form an
essentially small abelian subcategory of `Mod(X_proét, 𝒪_E)` closed under kernels, cokernels and
extensions.

The truncation stability holds for any coefficient ring
(`AlgebraicGeometry.ProEtale.boundedConstructible_truncLE`,
`AlgebraicGeometry.ProEtale.boundedConstructible_truncGE`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

section Truncation

variable {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]

/-- The truncation `τ^{≤ n} K` of a bounded constructible complex is bounded constructible. -/
lemma boundedConstructible_truncLE
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (hK : boundedConstructible R K) (n : ℤ) :
    boundedConstructible R ((DerivedCategory.TStructure.t.truncLE n).obj K) := by
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff R K).1 hK
  refine (mem_boundedConstructible_iff R _).2 ⟨⟨a, b, fun m hm ↦ ?_⟩, fun m ↦ ?_⟩ <;>
    by_cases hmn : m ≤ n
  · have := DerivedCategory.isIso_homologyFunctor_map_truncLEι_app n m hmn K
    exact (hab m hm).of_iso (asIso ((DerivedCategory.homologyFunctor _ m).map
      ((DerivedCategory.TStructure.t.truncLEι n).app K)))
  · exact DerivedCategory.isZero_of_isLE _ n _ (by lia)
  · have := DerivedCategory.isIso_homologyFunctor_map_truncLEι_app n m hmn K
    exact constructible_of_iso (asIso ((DerivedCategory.homologyFunctor _ m).map
      ((DerivedCategory.TStructure.t.truncLEι n).app K))).symm (hc m)
  · exact isConstructibleModuleObject_of_isZero R
      (DerivedCategory.isZero_of_isLE _ n _ (by lia))

/-- The truncation `τ^{≥ n} K` of a bounded constructible complex is bounded constructible. -/
lemma boundedConstructible_truncGE
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (hK : boundedConstructible R K) (n : ℤ) :
    boundedConstructible R ((DerivedCategory.TStructure.t.truncGE n).obj K) := by
  obtain ⟨⟨a, b, hab⟩, hc⟩ := (mem_boundedConstructible_iff R K).1 hK
  refine (mem_boundedConstructible_iff R _).2 ⟨⟨a, b, fun m hm ↦ ?_⟩, fun m ↦ ?_⟩ <;>
    by_cases hmn : n ≤ m
  · have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K n m hmn
    exact (hab m hm).of_iso (asIso ((DerivedCategory.homologyFunctor _ m).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app K))).symm
  · exact DerivedCategory.isZero_of_isGE _ n _ (by lia)
  · have := DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K n m hmn
    exact constructible_of_iso (asIso ((DerivedCategory.homologyFunctor _ m).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app K))) (hc m)
  · exact isConstructibleModuleObject_of_isZero R
      (DerivedCategory.isZero_of_isGE _ n _ (by lia))

/-- A complex concentrated in degree `0` is bounded constructible if and only if its
cohomology sheaf in degree `0` is constructible. -/
lemma boundedConstructible_iff_of_isLE_of_isGE
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    [K.IsLE 0] [K.IsGE 0] :
    boundedConstructible R K ↔
      IsConstructibleModuleObject R ((DerivedCategory.homologyFunctor _ 0).obj K) := by
  refine ⟨fun hK ↦ hK.2 0, fun hK ↦ (mem_boundedConstructible_iff R K).2
    ⟨⟨0, 0, fun m hm ↦ ?_⟩, fun m ↦ ?_⟩⟩
  · rcases hm with hm | hm
    · exact DerivedCategory.isZero_of_isGE _ 0 _ hm
    · exact DerivedCategory.isZero_of_isLE _ 0 _ hm
  · rcases lt_trichotomy m 0 with hm | rfl | hm
    · exact isConstructibleModuleObject_of_isZero R (DerivedCategory.isZero_of_isGE _ 0 _ hm)
    · exact hK
    · exact isConstructibleModuleObject_of_isZero R (DerivedCategory.isZero_of_isLE _ 0 _ hm)

/-- A sheaf of modules placed in degree `0` is a bounded constructible complex if and only if it
is constructible. -/
lemma boundedConstructible_singleFunctor_obj_zero_iff
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    boundedConstructible R ((DerivedCategory.singleFunctor _ 0).obj M) ↔
      IsConstructibleModuleObject R M := by
  rw [boundedConstructible_iff_of_isLE_of_isGE]
  exact ⟨constructible_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M),
    constructible_of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm⟩

end Truncation

namespace CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (X : Scheme.{u}) [IsNoetherian X]

set_option hygiene false in
/-- The coefficient ring object `𝒪_{E,X}`. -/
local notation "𝒪X" => condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E) X

/-- The constructible `𝒪_E`-sheaves on a noetherian scheme are closed under finite products. -/
lemma isClosedUnderFiniteProducts_isConstructibleModuleObject_padicIntegersRingObj :
    ObjectProperty.IsClosedUnderFiniteProducts (IsConstructibleModuleObject 𝒪X) :=
  let P : ObjectProperty (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) 𝒪X) :=
    IsConstructibleModuleObject 𝒪X
  have : P.IsClosedUnderExtensions :=
    (isConstructibleModuleObject_serre_padicIntegersRingObj ℓ X E).2.2
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ constructible_of_iso e h⟩
  have : P.ContainsZero :=
    ⟨0, isZero_zero _, isConstructibleModuleObject_of_isZero _ (isZero_zero _)⟩
  P.isClosedUnderFiniteProducts_of_isClosedUnderExtensions

/-- Blueprint `lemma-structure-integral-constructible-complexes--1`: for a finite subextension
`E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and a noetherian scheme `X`, `Dᵇc(X, 𝒪_E)` is a triangulated subcategory of
`D(X_proét, 𝒪_E)` of bounded objects, stable under the truncations `τ^{≤ n}` and `τ^{≥ n}`; its
objects in degree `0` (the complexes concentrated in degree `0`, equivalently the sheaves placed
in degree `0`) are the constructible sheaves `Cons(X, 𝒪_E)`, which form an essentially small
abelian subcategory of `Mod(X_proét, 𝒪_E)`, closed under kernels, cokernels (so that the
inclusion is exact) and extensions. -/
theorem boundedConstructible_padicIntegersRingObj_structure :
    (boundedConstructible 𝒪X).IsTriangulated ∧
      boundedConstructible 𝒪X ≤ DerivedCategory.TStructure.t.bounded ∧
      (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) 𝒪X)) (n : ℤ),
        boundedConstructible 𝒪X K →
          boundedConstructible 𝒪X ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
            boundedConstructible 𝒪X ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
      (∀ (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) 𝒪X)),
        K.IsLE 0 → K.IsGE 0 → (boundedConstructible 𝒪X K ↔
          IsConstructibleModuleObject 𝒪X ((DerivedCategory.homologyFunctor _ 0).obj K))) ∧
      (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) 𝒪X,
        boundedConstructible 𝒪X ((DerivedCategory.singleFunctor _ 0).obj M) ↔
          IsConstructibleModuleObject 𝒪X M) ∧
      EssentiallySmall.{u + 1} (ObjectProperty.FullSubcategory (IsConstructibleModuleObject 𝒪X)) ∧
      Nonempty (Abelian (ObjectProperty.FullSubcategory (IsConstructibleModuleObject 𝒪X))) ∧
      ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject 𝒪X) ∧
      ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject 𝒪X) ∧
      ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject 𝒪X) := by
  obtain ⟨hk, hc, he⟩ := isConstructibleModuleObject_serre_padicIntegersRingObj ℓ X E
  have : ObjectProperty.EssentiallySmall.{u + 1} (IsConstructibleModuleObject 𝒪X) :=
    constructibleModuleObjects_essentiallySmall X 𝒪X
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject 𝒪X) :=
    ⟨0, isZero_zero _, isConstructibleModuleObject_of_isZero _ (isZero_zero _)⟩
  have := isClosedUnderFiniteProducts_isConstructibleModuleObject_padicIntegersRingObj ℓ E X
  exact ⟨inferInstance, fun _ hK ↦ hK.1,
    fun K n hK ↦ ⟨boundedConstructible_truncLE 𝒪X hK n, boundedConstructible_truncGE 𝒪X hK n⟩,
    fun K _ _ ↦ boundedConstructible_iff_of_isLE_of_isGE 𝒪X K,
    boundedConstructible_singleFunctor_obj_zero_iff 𝒪X, inferInstance, ⟨inferInstance⟩,
    hk, hc, he⟩

end CondensedRing

end AlgebraicGeometry.ProEtale
