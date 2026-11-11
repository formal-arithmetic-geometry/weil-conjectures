/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality

/-!
# `Rf^!` is local on the source and on the target

For finite coefficients `Λ` and a morphism `f : X ⟶ Y` admitting a compactification, the
exceptional inverse image `Rf^!` can be computed locally for open coverings:

* on the source: for an open cover `{U_i ⟶ X}`, the restriction of `Rf^!` to `U_i` is
  `R(U_i ⟶ X ⟶ Y)^!`, and isomorphisms on `X` are detected on the `U_i`;
* on the target: for an open cover `{V_i ⟶ Y}` with preimages `X_i = X ×_Y V_i`, the base change
  map `Rf^! ⋙ L(X_i ⟶ X)^* ⟶ L(V_i ⟶ Y)^* ⋙ R(X_i ⟶ V_i)^!` is an isomorphism, and
  isomorphisms on `X` are detected on the `X_i`.

These are the last two clauses of blueprint
`proposition-composition-open-restriction-compactifications-f`.

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedUpperShriek_local_source`
- `AlgebraicGeometry.Etale.rightDerivedUpperShriek_local_target`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}}

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--7`: **`Rf^!` can be
computed locally on `X` for open coverings**. For an open cover `{j_i : U_i ⟶ X}` of `X` by
quasi-compact open immersions with `j_i ≫ f` admitting compactifications, the restriction
`j_i^* Rf^!` is `R(j_i ≫ f)^!`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_openImmersion`), and a
morphism of `D(X_ét, Λ)` is an isomorphism if and only if all its restrictions to the `U_i` are
(`AlgebraicGeometry.Etale.isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_jointlySurjective`).
-/
theorem rightDerivedUpperShriek_local_source (f : X ⟶ Y) [HasCompactification f]
    (𝒰 : Scheme.OpenCover.{u} X) [∀ i, QuasiCompact (𝒰.f i)]
    [∀ i, HasCompactification (𝒰.f i ≫ f)] [∀ i, QuasiCompact (𝒰.f i ≫ f)] :
    (∀ i, Nonempty (R(f)^![Λ] ⋙ D((𝒰.f i)^*[ModuleCat.{u + 1} Λ]) ≅
      R(𝒰.f i ≫ f)^![Λ])) ∧
    ∀ {M N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : M ⟶ N),
      IsIso φ ↔ ∀ i, IsIso (D((𝒰.f i)^*[ModuleCat.{u + 1} Λ]).map φ) := by
  refine ⟨fun i ↦ ?_, fun φ ↦ ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩⟩
  · have : HasCompactification (𝒰.f i) :=
      (Compactification.ofIsOpenImmersion (𝒰.f i)).hasCompactification
    exact nonempty_iso_rightDerivedUpperShriek_comp_openImmersion Λ (𝒰.f i) f
  · exact isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_jointlySurjective Λ 𝒰.f
      (fun x ↦ 𝒰.exists_eq x) φ h

/-- Blueprint `proposition-composition-open-restriction-compactifications-f--8`: **`Rf^!` can be
computed locally on `Y` for open coverings**. For an open cover `{v_i : V_i ⟶ Y}` of `Y`, write
`u_i : X_i = X ×_Y V_i ⟶ X` and `f_i : X_i ⟶ V_i` for the projections. Then the base change maps
`Rf^! ⋙ Lu_i^* ⟶ Lv_i^* ⋙ Rf_i^!`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) are isomorphisms
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion`), and
since the `X_i` cover `X`, a morphism of `D(X_ét, Λ)` is an isomorphism if and only if all its
restrictions to the `X_i` are. -/
theorem rightDerivedUpperShriek_local_target (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (𝒱 : Scheme.OpenCover.{u} Y) :
    (∀ i, IsIso (rightDerivedUpperShriekBaseChangeMap Λ (IsPullback.of_hasPullback f (𝒱.f i)))) ∧
    ∀ {M N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (φ : M ⟶ N),
      IsIso φ ↔ ∀ i, IsIso (L((pullback.fst f (𝒱.f i))^*[ModuleCat.{u + 1} Λ]).map φ) := by
  refine ⟨fun i ↦ isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion Λ _,
    fun φ ↦ ⟨fun _ _ ↦ inferInstance, fun h ↦ ?_⟩⟩
  refine isIso_of_isIso_mapDerivedCategoryUpperStar_map_of_jointlySurjective Λ
    (fun i ↦ pullback.fst f (𝒱.f i)) (fun x ↦ ?_) φ fun i ↦ ?_
  · obtain ⟨i, y, hy⟩ := 𝒱.exists_eq (f x)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
    exact ⟨i, z, hz⟩
  · exact (NatIso.isIso_map_iff
      (leftDerivedUpperStarIsoMapDerivedCategory _ (pullback.fst f (𝒱.f i))) φ).1 (h i)

end Etale

end AlgebraicGeometry
