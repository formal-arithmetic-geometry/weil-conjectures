/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.TraceFormula.TotalSiteInjectiveAugmentationExactness
public import Sheaf.TraceFormula.TotalSiteFreeModuleResolution
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Injective augmented Čech resolution on a total simplicial site

Source: Stacks Project, `spaces-simplicial.tex`, Tags 0D72, 0D7C and 0D7D
(blueprint: lem-trf-total-site-injective-cech-resolution).

The datum below uses the canonical constant-module categories and the coherent
augmentation presentation.  In particular, transition and augmentation comparisons
are required to satisfy the unit, compositor, mate, and total-inverse equations; they
are not independent natural isomorphisms.

The transitions `u` and augmentations `a` of the datum are geometric-morphism data
(`CategoryTheory.GeometricMorphism`, blueprint: def-trf-geometric-morphism) directly on
the constant-module categories, with exact transition inverse images
(`TotalSiteSystemData.pull_exact`).  The node's case is the instance whose functors are
the canonical constant-coefficient module inverse and direct images of the site
geometric morphisms (lem-pe-constant-left-module-inverse-image,
lem-weil-pbc-geometric-module-transport); the theorem is stated for every such coherent
datum, so it contains that case and assumes nothing more.  The `Abelian` instances on
the module categories are hypotheses; on small sites they are supplied by Mathlib's
`SheafOfModules` instance, whose preadditive structure is the canonical one.
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false

universe c d t v w z

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

/-- Modules over the sheafified constant coefficient ring on a site.
Source: Stacks, Sites, 00YV (blueprint: def-weil-sheaf-of-modules-category). -/
abbrev constantModuleCategory (C : Type c) [Category.{v} C]
    (J : GrothendieckTopology C) (Λ : Type z) [CommRing Λ]
    [HasWeakSheafify J RingCat] :=
  ringedSiteModules.{v, z} ((constantSheaf J RingCat).obj (RingCat.of Λ))

/-- Coherent total-site augmentation data on canonical constant-module categories.
The single field `data` is the normalized geometric augmentation presentation
`TotalSiteAugmentationData` of `TotalSiteInjectiveAugmentationExactness`, taken with the
component categories `constantModuleCategory (C i) (J i) Λ`, the total category `T` and
the base `constantModuleCategory D JD Λ`: the transition and augmentation geometric
morphisms on module categories, their unit, compositor and mate coherences, the
fully faithful and essentially surjective presentation of all compatible module
families by `T`, and the total augmentation with its inverse-image identification.
Source: Stacks, Tags 00YV, 09WF and 0D7D
(blueprint: lem-trf-total-site-injective-cech-resolution). -/
structure TotalSiteModuleCechData
    {C : SimplexCategoryᵒᵖ → Type c} [∀ i, Category.{v} (C i)]
    {J : ∀ i, GrothendieckTopology (C i)}
    {D : Type d} [Category.{w} D] {JD : GrothendieckTopology D}
    {Λ : Type z} [CommRing Λ] [∀ i, HasWeakSheafify (J i) RingCat]
    [HasWeakSheafify JD RingCat]
    [abelianC : ∀ i, Abelian (constantModuleCategory (C i) (J i) Λ)]
    [abelianD : Abelian (constantModuleCategory D JD Λ)]
    (T : Type t) [Category.{max c v} T] [Abelian T] where
  data : @TotalSiteAugmentationData _ _ abelianC T _ inferInstance _ _ abelianD

/-- The component restriction with the preadditive structure stored by the coherent
augmentation datum.  This explicit projection keeps the module category's chosen
preadditive instance definitionally aligned with `TotalSiteAugmentationData.system`.
Source: Stacks, Tag 09WF (blueprint: lem-trf-total-site-injective-cech-resolution). -/
noncomputable def totalSiteComponent
    {C : SimplexCategoryᵒᵖ → Type c} [∀ i, Category.{v} (C i)]
    {J : ∀ i, GrothendieckTopology (C i)} {D : Type d} [Category.{w} D]
    {JD : GrothendieckTopology D} {Λ : Type z} [CommRing Λ]
    [∀ i, HasWeakSheafify (J i) RingCat] [HasWeakSheafify JD RingCat]
    [∀ i, Abelian (constantModuleCategory (C i) (J i) Λ)]
    [Abelian (constantModuleCategory D JD Λ)]
    {T : Type t} [Category.{max c v} T] [Abelian T]
    (S : TotalSiteAugmentationData
      (fun j => constantModuleCategory (C j) (J j) Λ) T
      (constantModuleCategory D JD Λ)) (i : SimplexCategoryᵒᵖ) :
      T ⥤ constantModuleCategory (C i) (J i) Λ :=
  @TotalSiteSystemData.component _ _ _ _ _ _ _ _
    (fun j => (inferInstance : Abelian (constantModuleCategory (C j) (J j) Λ)).toPreadditive)
    S.system i


/-- The canonical augmented alternating coface complex for an injective total module is
exact, remains exact after Hom from any canonical constant module, and is natural in the
injective. Source: Stacks, Tag 0D7D (blueprint: lem-trf-total-site-injective-cech-resolution).

Proof (postponed): (1) use the normalized constant-module inverse-image lifts and the
coherent compatible-system presentation; their unit and compositor laws give the total
module category and identify the component restrictions. (2) Apply the free simplex
resolution of Tag 0D7C and its identity-summand Hom bijection, transporting along the
module adjunctions and the normalized augmentation comparisons. (3) The extra-degeneracy
contraction gives exactness of the alternating complex; exact inverse images make kernels,
images, and cokernels componentwise, and the conservative component restrictions detect
exactness. (4) Injectivity extends Hom cocycles through images, proving the Hom clauses;
Yoneda kernel tests prove the displayed module sequence and monicity. (5) The same
normalized mate equations prove the augmentation and differential naturality clauses. -/
theorem totalSite_injective_cech_resolution
    {C : SimplexCategoryᵒᵖ → Type c} [∀ i, Category.{v} (C i)]
    {J : ∀ i, GrothendieckTopology (C i)} {D : Type d} [Category.{w} D]
    {JD : GrothendieckTopology D} {Λ : Type z} [CommRing Λ]
    [∀ i, HasWeakSheafify (J i) RingCat] [HasWeakSheafify JD RingCat]
    [∀ i, Abelian (constantModuleCategory (C i) (J i) Λ)]
    [Abelian (constantModuleCategory D JD Λ)]
    {T : Type t} [Category.{max c v} T] [Abelian T]
    (S : TotalSiteModuleCechData (C := C) (J := J) (D := D) (JD := JD)
      (Λ := Λ) T) (I : T) [Injective I] :
    letI : (∀ i, Preadditive (constantModuleCategory (C i) (J i) Λ)) :=
      fun i => (inferInstance : Abelian (constantModuleCategory (C i) (J i) Λ)).toPreadditive
    letI : Preadditive (constantModuleCategory D JD Λ) :=
      (inferInstance : Abelian (constantModuleCategory D JD Λ)).toPreadditive
    (∃ h₀ : S.data.augmentation I ≫
        S.data.differential I 0 = 0,
      Mono (S.data.augmentation I) ∧
        (ShortComplex.mk (S.data.augmentation I)
          (S.data.differential I 0) h₀).Exact) ∧
    (∀ p : ℕ, ∃ hₚ : S.data.differential I p ≫
        S.data.differential I (p + 1) = 0,
      (ShortComplex.mk (S.data.differential I p)
        (S.data.differential I (p + 1)) hₚ).Exact) ∧
    (∀ G : constantModuleCategory D JD Λ,
      Function.Injective (fun h : G ⟶ S.data.total.direct.obj I =>
        h ≫ S.data.augmentation I) ∧
      Function.Exact
        (fun h : G ⟶ S.data.total.direct.obj I =>
          h ≫ S.data.augmentation I)
        (fun h : G ⟶
          (S.data.a (Opposite.op (SimplexCategory.mk 0))).direct.obj
            ((totalSiteComponent S.data (Opposite.op (SimplexCategory.mk 0))).obj I) =>
          h ≫ S.data.differential I 0) ∧
      ∀ p : ℕ,
        Function.Exact
          (fun h : G ⟶
            (S.data.a (Opposite.op (SimplexCategory.mk p))).direct.obj
              ((totalSiteComponent S.data (Opposite.op (SimplexCategory.mk p))).obj I) =>
            h ≫ S.data.differential I p)
          (fun h : G ⟶
            (S.data.a (Opposite.op (SimplexCategory.mk (p + 1)))).direct.obj
              ((totalSiteComponent S.data (Opposite.op (SimplexCategory.mk (p + 1)))).obj I) =>
            h ≫ S.data.differential I (p + 1))) ∧
    ∀ {I' : T} [Injective I'] (f : I ⟶ I'),
      S.data.total.direct.map f ≫ S.data.augmentation I' =
        S.data.augmentation I ≫
          (S.data.a (Opposite.op (SimplexCategory.mk 0))).direct.map
            ((totalSiteComponent S.data (Opposite.op (SimplexCategory.mk 0))).map f) ∧
      ∀ p : ℕ,
        (S.data.a (Opposite.op (SimplexCategory.mk p))).direct.map
            ((totalSiteComponent S.data (Opposite.op (SimplexCategory.mk p))).map f) ≫
            S.data.differential I' p =
          S.data.differential I p ≫
            (S.data.a (Opposite.op (SimplexCategory.mk (p + 1)))).direct.map
              ((totalSiteComponent S.data (Opposite.op (SimplexCategory.mk (p + 1)))).map f) := by
  sorry

end CategoryTheory
