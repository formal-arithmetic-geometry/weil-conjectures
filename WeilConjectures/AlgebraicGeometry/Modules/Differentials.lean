/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# The sheaf of relative differentials of a morphism of schemes

For a morphism of schemes `f : X ⟶ S`, the sheaf `Ω¹_{X/S}` of relative Kähler differentials is
the sheafification of the presheaf of `𝒪_X`-modules `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_S)(U)}`. Here
`f⁻¹𝒪_S` is the presheaf inverse image `AlgebraicGeometry.Scheme.Hom.pullbackPresheaf`, not its
sheafification.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`: the sheaf `Ω¹_{X/S}`.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsDerivation`: the derivation
  `d : 𝒪_X → Ω¹_{X/S}`, relative to `f⁻¹𝒪_S ⟶ 𝒪_X`.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsHomEquiv`: the universal property of `d`:
  for a sheaf of `𝒪_X`-modules `M`, morphisms `Ω¹_{X/S} ⟶ M` are the same as
  `f⁻¹𝒪_S`-linear derivations `𝒪_X → M`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentials`: `Ω¹_{X/S} = 0` for an open
  immersion `f`; in particular `Ω¹_{X/X} = 0` (`isZero_relativeDifferentials_id`).
- `AlgebraicGeometry.Scheme.Hom.nonempty_relativeDifferentials_Spec_iso_tilde`: for an
  `A`-algebra `B`, `Ω¹_{Spec B / Spec A}` is the quasi-coherent sheaf `Ω[B⁄A]^~`.
- `AlgebraicGeometry.Scheme.Hom.nonempty_relativeDifferentials_Spec_Γ_linearEquiv`: for an
  `A`-algebra `B`, `Γ(Spec B, Ω¹_{Spec B / Spec A}) ≃ Ω[B⁄A]` as `B`-modules.

## TODO

- Show that the definition does not change when `f⁻¹𝒪_S` is replaced by its sheafification,
  which is the inverse image used in the Stacks project.

## References

- [Stacks: Section 01UM, sheaf of differentials of a morphism of schemes](https://stacks.math.columbia.edu/tag/01UM)
- [Stacks: Section 08RL, differentials of sheaves of rings](https://stacks.math.columbia.edu/tag/08RL)
-/

@[expose] public section

universe u

open CategoryTheory Limits PresheafOfModules PresheafOfModules.DifferentialsConstruction

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The sheaf of relative Kähler differentials `Ω¹_{X/S}` of a morphism of schemes `f : X ⟶ S`:
the sheafification of the presheaf `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_S)(U)}`. -/
@[stacks 01UM]
noncomputable def relativeDifferentials : X.Modules :=
  (sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (relativeDifferentials' f.pullbackPresheafToPresheaf)

/-- The universal derivation `d : 𝒪_X → Ω¹_{X/S}`, relative to `f⁻¹𝒪_S ⟶ 𝒪_X`: the universal
derivation into the presheaf of differentials, composed with the sheafification unit. -/
noncomputable def relativeDifferentialsDerivation :
    f.relativeDifferentials.val.Derivation' f.pullbackPresheafToPresheaf :=
  (derivation' f.pullbackPresheafToPresheaf).postcomp
    ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _)

/-- The universal property of `d : 𝒪_X → Ω¹_{X/S}`: for a sheaf of `𝒪_X`-modules `M`,
composing with `d` identifies morphisms `Ω¹_{X/S} ⟶ M` with `f⁻¹𝒪_S`-linear derivations
`𝒪_X → M`. -/
noncomputable def relativeDifferentialsHomEquiv (M : X.Modules) :
    (f.relativeDifferentials ⟶ M) ≃ M.val.Derivation' f.pullbackPresheafToPresheaf where
  toFun g := f.relativeDifferentialsDerivation.postcomp g.val
  invFun D := ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
    ((isUniversal' f.pullbackPresheafToPresheaf).desc D)
  left_inv g := by
    apply ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply (isUniversal' f.pullbackPresheafToPresheaf).postcomp_injective
    rw [Derivation.Universal.fac]
    rfl
  right_inv D := by
    change (derivation' f.pullbackPresheafToPresheaf).postcomp
      (((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _)
        (((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm _)) = D
    rw [Equiv.apply_symm_apply, Derivation.Universal.fac]

@[simp]
lemma relativeDifferentialsHomEquiv_apply {M : X.Modules} (g : f.relativeDifferentials ⟶ M) :
    f.relativeDifferentialsHomEquiv M g = f.relativeDifferentialsDerivation.postcomp g.val :=
  rfl

/-- If `f⁻¹𝒪_S ⟶ 𝒪_X` is surjective on sections, then `Ω¹_{X/S} = 0`. -/
lemma isZero_relativeDifferentials_of_surjective
    (h : ∀ U, Function.Surjective (f.pullbackPresheafToPresheaf.app U)) :
    IsZero f.relativeDifferentials := by
  rw [IsZero.iff_id_eq_zero]
  apply (f.relativeDifferentialsHomEquiv _).injective
  ext U x
  obtain ⟨a, rfl⟩ := h U x
  simp only [relativeDifferentialsHomEquiv_apply, Derivation.postcomp_d_apply]
  erw [Derivation'.d_app]
  simp

/-- The sheaf of relative differentials of an open immersion vanishes. -/
lemma isZero_relativeDifferentials [IsOpenImmersion f] : IsZero f.relativeDifferentials := by
  refine f.isZero_relativeDifferentials_of_surjective fun U y ↦ ?_
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.appIso U.unop).hom).2 y
  rw [appIso_hom', appLE_eq_pullbackPresheafToPresheaf_app]
  exact ⟨_, rfl⟩

variable (X) in
/-- The sheaf of relative differentials of the identity morphism vanishes: `Ω¹_{X/X} = 0`. -/
lemma isZero_relativeDifferentials_id : IsZero (𝟙 X : X ⟶ X).relativeDifferentials :=
  isZero_relativeDifferentials _

section Affine

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- For an `A`-algebra `B`, the sheaf of relative differentials `Ω¹_{Spec B / Spec A}` is the
quasi-coherent sheaf `Ω[B⁄A]^~` associated to the `B`-module of Kähler differentials. -/
lemma nonempty_relativeDifferentials_Spec_iso_tilde :
    Nonempty ((Spec.map (CommRingCat.ofHom (algebraMap A B))).relativeDifferentials ≅
      tilde (ModuleCat.of (CommRingCat.of B) Ω[B⁄A])) := by
  sorry

/-- For an `A`-algebra `B`, the global sections of the sheaf of relative differentials
`Ω¹_{Spec B / Spec A}`, with their `B`-module structure from `moduleSpecΓFunctor`, are the
`B`-module `Ω[B⁄A]` of Kähler differentials. -/
lemma nonempty_relativeDifferentials_Spec_Γ_linearEquiv :
    Nonempty ((moduleSpecΓFunctor (R := .of B)).obj
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).relativeDifferentials ≃ₗ[B] Ω[B⁄A]) := by
  sorry

end Affine

end AlgebraicGeometry.Scheme.Hom
