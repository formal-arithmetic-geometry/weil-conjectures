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
- `AlgebraicGeometry.relativeDifferentialsSpecTildeHom`: for a ring map `φ : R ⟶ S`, the
  canonical morphism `Ω_{S/R}^~ ⟶ Ω¹_{Spec S / Spec R}`, adjoint to the map
  `relativeDifferentialsSpecΓHom : Ω_{S/R} → Γ(Spec S, Ω¹)` sending `D b` to `d b`.
- `AlgebraicGeometry.relativeDifferentialsSpecIso`: the isomorphism
  `Ω¹_{Spec S / Spec R} ≅ Ω_{S/R}^~`.
- `AlgebraicGeometry.relativeDifferentialsSpecΓIso`: the isomorphism
  `Γ(Spec S, Ω¹_{Spec S / Spec R}) ≅ Ω_{S/R}` of `S`-modules, compatible with `d` and `D`.

For an `A`-algebra `B`, apply these to `φ = CommRingCat.ofHom (algebraMap A B)`; then
`CommRingCat.KaehlerDifferential φ` is `Ω[B⁄A]` for the algebra structure `φ.hom.toAlgebra`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentials`: `Ω¹_{X/S} = 0` for an open
  immersion `f`; in particular `Ω¹_{X/X} = 0` (`isZero_relativeDifferentials_id`).
- `AlgebraicGeometry.isIso_relativeDifferentialsSpecTildeHom`: the canonical morphism
  `Ω_{S/R}^~ ⟶ Ω¹_{Spec S / Spec R}` is an isomorphism (currently `sorry`).

## TODO

- Show that the definition does not change when `f⁻¹𝒪_S` is replaced by its sheafification,
  which is the inverse image used in the Stacks project.
- Prove `isIso_relativeDifferentialsSpecTildeHom`, e.g. via Stacks 01UO (derivations into a sheaf
  on `Spec S` are determined by their global sections).
- Deduce the local statement: for affine opens `U ⊆ X` and `V ⊆ S` with `f(U) ⊆ V`,
  `Ω¹_{X/S}|_U ≅ Ω_{𝒪(U)/𝒪(V)}^~`, and hence that `Ω¹_{X/S}` is quasi-coherent.

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

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

section Affine

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- For a ring map `φ : R ⟶ S`, the global sections of `d : 𝒪 → Ω¹_{Spec S / Spec R}` form an
`R`-derivation `S → Γ(Spec S, Ω¹_{Spec S / Spec R})`. -/
noncomputable def relativeDifferentialsSpecΓDerivation :
    ((moduleSpecΓFunctor (R := S)).obj (Spec.map φ).relativeDifferentials).Derivation φ :=
  ModuleCat.Derivation.mk
    (fun b ↦ (Spec.map φ).relativeDifferentialsDerivation.d (X := .op ⊤)
      ((Scheme.ΓSpecIso S).inv b))
    (fun b b' ↦ by simp)
    (fun b b' ↦ by
      rw [← Scheme.ΓSpecIso_inv_mul]
      exact (Spec.map φ).relativeDifferentialsDerivation.d_mul _ _)
    (fun a ↦ by
      rw [← Scheme.specMap_appTop_ΓSpecIso_inv, ← Scheme.Hom.appLE_top_top _ le_top,
        Scheme.Hom.appLE_eq_pullbackPresheafToPresheaf_app]
      exact PresheafOfModules.Derivation'.d_app _ _)

/-- For a ring map `φ : R ⟶ S`, the `S`-linear map `Ω_{S/R} → Γ(Spec S, Ω¹_{Spec S / Spec R})`
sending `D b` to `d b`, given by the universal property of Kähler differentials. -/
noncomputable def relativeDifferentialsSpecΓHom :
    CommRingCat.KaehlerDifferential φ ⟶
      (moduleSpecΓFunctor (R := S)).obj (Spec.map φ).relativeDifferentials :=
  (relativeDifferentialsSpecΓDerivation φ).desc

/-- The map `Ω_{S/R} → Γ(Spec S, Ω¹_{Spec S / Spec R})` sends `D b` to `d b`. -/
@[simp]
lemma relativeDifferentialsSpecΓHom_d (b : S) :
    relativeDifferentialsSpecΓHom φ (CommRingCat.KaehlerDifferential.d b) =
      (Spec.map φ).relativeDifferentialsDerivation.d (X := .op ⊤) ((Scheme.ΓSpecIso S).inv b) :=
  (relativeDifferentialsSpecΓDerivation φ).desc_d b

/-- For a ring map `φ : R ⟶ S`, the canonical morphism `Ω_{S/R}^~ ⟶ Ω¹_{Spec S / Spec R}`,
adjoint to `relativeDifferentialsSpecΓHom` under `tilde ⊣ Γ`. -/
noncomputable def relativeDifferentialsSpecTildeHom :
    tilde (CommRingCat.KaehlerDifferential φ) ⟶ (Spec.map φ).relativeDifferentials :=
  (tilde.adjunction.homEquiv _ _).symm (relativeDifferentialsSpecΓHom φ)

/-- On global sections, `relativeDifferentialsSpecTildeHom` is `relativeDifferentialsSpecΓHom`,
after identifying `Γ(Spec S, Ω_{S/R}^~)` with `Ω_{S/R}`. -/
@[reassoc (attr := simp)]
lemma unit_app_comp_map_relativeDifferentialsSpecTildeHom :
    tilde.adjunction.unit.app _ ≫
        (moduleSpecΓFunctor (R := S)).map (relativeDifferentialsSpecTildeHom φ) =
      relativeDifferentialsSpecΓHom φ :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans ((tilde.adjunction.homEquiv _ _).apply_symm_apply _)

/-- The canonical morphism `Ω_{S/R}^~ ⟶ Ω¹_{Spec S / Spec R}` is an isomorphism. -/
instance isIso_relativeDifferentialsSpecTildeHom :
    IsIso (relativeDifferentialsSpecTildeHom φ) := by
  sorry

/-- The map `Ω_{S/R} → Γ(Spec S, Ω¹_{Spec S / Spec R})` is an isomorphism. -/
instance isIso_relativeDifferentialsSpecΓHom : IsIso (relativeDifferentialsSpecΓHom φ) := by
  rw [← unit_app_comp_map_relativeDifferentialsSpecTildeHom]
  exact IsIso.comp_isIso' inferInstance
    (inferInstanceAs (IsIso ((moduleSpecΓFunctor).map (relativeDifferentialsSpecTildeHom φ))))

/-- For a ring map `φ : R ⟶ S`, the sheaf of relative differentials `Ω¹_{Spec S / Spec R}` is
isomorphic to the quasi-coherent sheaf `Ω_{S/R}^~`, via the inverse of
`relativeDifferentialsSpecTildeHom`. -/
noncomputable def relativeDifferentialsSpecIso :
    (Spec.map φ).relativeDifferentials ≅ tilde (CommRingCat.KaehlerDifferential φ) :=
  (asIso (relativeDifferentialsSpecTildeHom φ)).symm

/-- For a ring map `φ : R ⟶ S`, the global sections of `Ω¹_{Spec S / Spec R}` are the `S`-module
`Ω_{S/R}`, compatibly with `d` and `D` (`relativeDifferentialsSpecΓHom_d`). -/
@[stacks 01UT]
noncomputable def relativeDifferentialsSpecΓIso :
    (moduleSpecΓFunctor (R := S)).obj (Spec.map φ).relativeDifferentials ≅
      CommRingCat.KaehlerDifferential φ :=
  (asIso (relativeDifferentialsSpecΓHom φ)).symm

end Affine

end AlgebraicGeometry
