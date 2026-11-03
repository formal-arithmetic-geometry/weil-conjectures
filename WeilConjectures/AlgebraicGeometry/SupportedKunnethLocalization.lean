/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Supported.SupportedProductLocalization
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct

import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProductSupportMaps
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Supported Künneth: reduction to full supports by localization

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
lem-pur-kunneth-supported.proof.md, paragraphs 1--3
(blueprint: lem-pur-kunneth-supported-localization-reduction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private lemma support_eq_compat (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) {U V : T.Opens} (h : U = V) :
    (eqToIso (congrArg (supportedEtaleSections A T) h)).hom ≫
      supportedEtaleSectionsι A T V = supportedEtaleSectionsι A T U := by
  subst V
  simp

private lemma isIso_product_support_congr (A : Type (u + 1)) [CommRing A]
    {S X Y B B' D D' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (b' : B' ⟶ X) (d : D ⟶ Y) (d' : D' ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion b']
    [IsClosedImmersion d] [IsClosedImmersion d']
    (hb : b.openComplement = b'.openComplement)
    (hd : d.openComplement = d'.openComplement)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    IsIso (supportedExteriorProduct A f g b d K L) ↔
      IsIso (supportedExteriorProduct A f g b' d' K L) := by
  have hp : (supportedProductImmersion f g b d).openComplement =
      (supportedProductImmersion f g b' d').openComplement := by
    apply TopologicalSpace.Opens.ext
    have hb' := congrArg (fun U : X.Opens => (U : Set X)) hb
    have hd' := congrArg (fun U : Y.Opens => (U : Set Y)) hd
    simp only [Scheme.Hom.coe_openComplement] at hb' hd' ⊢
    simp only [supportedProductImmersion, Scheme.Pullback.range_map,
      Set.compl_inter]
    simp only [← Set.preimage_compl, hb', hd']
  let r₁ := (eqToIso (congrArg (supportedEtaleSections A X) hb)).hom
  let r₂ := (eqToIso (congrArg (supportedEtaleSections A Y) hd)).hom
  let r₀ := (eqToIso (congrArg (supportedEtaleSections A (pullback f g)) hp)).hom
  have he := supportedExteriorProduct_supportMaps A f g b b' d d' r₁ r₂ r₀
    (support_eq_compat A X hb) (support_eq_compat A Y hd)
    (support_eq_compat A (pullback f g) hp) K L
  have : IsIso r₁ := inferInstance
  have : IsIso r₂ := inferInstance
  have : IsIso r₀ := inferInstance
  have hi := congrArg IsIso he
  simpa only [isIso_comp_right_iff, isIso_comp_left_iff] using hi.to_iff

private lemma intersection_id_complement {T C : Scheme.{u}} (c : C ⟶ T)
    [IsClosedImmersion c] :
    (supportIntersection (𝟙 T) c).openComplement = c.openComplement := by
  apply TopologicalSpace.Opens.ext
  change (Set.range (pullback.fst (𝟙 T) c ≫ 𝟙 T))ᶜ = (Set.range c)ᶜ
  rw [Scheme.Pullback.range_fst_comp]
  simp

private lemma onOpen_id_complement (T : Scheme.{u}) (U : T.Opens) :
    (supportOnOpen (𝟙 T) U).openComplement =
      (𝟙 U.toScheme : U.toScheme ⟶ U.toScheme).openComplement := by
  rw [supportOnOpen_complement]
  apply TopologicalSpace.Opens.ext
  simp [Scheme.Hom.coe_openComplement]

-- The second-variable triangle argument, used on both X × Y and U × Y.
private lemma isIso_second_localization
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y W : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (j : W ⟶ Y) [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE n)
    (hXY : IsIso (supportedExteriorProduct A f g (𝟙 X) (𝟙 Y) K.obj L.obj))
    (hXV : IsIso (supportedExteriorProduct A f (j.openComplement.ι ≫ g)
      (𝟙 X) (𝟙 j.openComplement.toScheme) K.obj
      ((upperStar (ModuleCat.{u + 1} A) j.openComplement.ι).mapDerivedCategory.obj L.obj))) :
    IsIso (supportedExteriorProduct A f g (𝟙 X) j K.obj L.obj) := by
  obtain ⟨hS, hT, m, hm₁, hm₂, hm₃⟩ :=
    supportedProductLocalizationSecond k A f g (𝟙 X) j (𝟙 Y) K L hF
  have h₂ : IsIso m.hom₂ := by
    simpa only [hm₂, supportedSecondLocalizationComponent₂] using hXY
  have hOpen : IsIso (supportedExteriorProduct A f (j.openComplement.ι ≫ g)
      (𝟙 X) (supportOnOpen (𝟙 Y) j.openComplement) K.obj
      ((upperStar (ModuleCat.{u + 1} A) j.openComplement.ι).mapDerivedCategory.obj
        L.obj)) :=
    (isIso_product_support_congr A _ _ (𝟙 X) (𝟙 X)
      (supportOnOpen (𝟙 Y) j.openComplement) (𝟙 j.openComplement.toScheme)
      rfl (onOpen_id_complement Y j.openComplement) _ _).2 hXV
  have h₃ : IsIso m.hom₃ := by
    rw [hm₃]
    dsimp only [supportedSecondLocalizationComponent₃]
    infer_instance
  have h₁ := isIso₁_of_isIso₂₃ m hS hT h₂ h₃
  rw [hm₁] at h₁
  dsimp only [supportedSecondLocalizationComponent₁] at h₁
  have hi : IsIso (supportedExteriorProduct A f g (𝟙 X)
      (supportIntersection (𝟙 Y) j) K.obj L.obj) :=
    (isIso_comp_right_iff _ _).1 h₁
  exact (isIso_product_support_congr A f g (𝟙 X) (𝟙 X)
    (supportIntersection (𝟙 Y) j) j rfl (intersection_id_complement j) _ _).1 hi

/--
Localization reduction for supported Künneth.  Over an algebraically closed field `k`
with a finite coefficient ring `A`, the four full-support maps on `X × Y`, `X × V`,
`U × Y` and `U × V` (`U = X \ Z`, `V = Y \ W`), together with a lower bound for the
external product, imply that the closed-support map `κ^{Z,W}` is an isomorphism.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
lem-pur-kunneth-supported.proof.md, paragraphs 1--3; Stacks 0F1P
(blueprint: lem-pur-kunneth-supported-localization-reduction).

Proof:
1. `F = K ⊠ L` is bounded below by `hF`, hence so are its restrictions to the open
   products. The second-variable clause of `supportedProductLocalizationSecond`
   (lem-pur-supported-product-localization, with `D' = X`, `B' = Y`, `C' = W`) gives a
   morphism of distinguished support-restriction triangles
   (lem-pur-support-restriction-triangle, def-pur-supported-localization-comparisons)
   with components `κ^{X,W}`, `κ^{X,Y}`, `κ^{X,V}`, including the boundary square. The
   last two are isomorphisms by `hXY`, `hXV`; the five lemma on the long exact
   cohomology sequences makes `κ^{X,W}` an isomorphism.
2. The same argument on `U × Y` with `K|_U, L` (`U → Spec k` is again separated of
   finite type), using `hUY`, `hUV`, makes `κ^{U,W}` an isomorphism.
3. The first-variable clause `supportedProductLocalizationFirst` (with `B = X`,
   `C = Z`, `D = W`) gives a morphism of distinguished triangles with components
   `κ^{Z,W}`, `κ^{X,W}`, `κ^{U,W}` and commuting boundary square; by Steps 1 and 2 and
   the five lemma in each degree, `κ^{Z,W}` is an isomorphism.
-/
theorem isIso_supportedExteriorProduct_of_localization
    (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hF : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE n)
    (hXY : IsIso (supportedExteriorProduct A f g (𝟙 X) (𝟙 Y) K.obj L.obj))
    (hXV : IsIso (supportedExteriorProduct A f (j.openComplement.ι ≫ g)
      (𝟙 X) (𝟙 j.openComplement.toScheme) K.obj
      ((upperStar (ModuleCat.{u + 1} A) j.openComplement.ι).mapDerivedCategory.obj L.obj)))
    (hUY : IsIso (supportedExteriorProduct A (i.openComplement.ι ≫ f) g
      (𝟙 i.openComplement.toScheme) (𝟙 Y)
      ((upperStar (ModuleCat.{u + 1} A) i.openComplement.ι).mapDerivedCategory.obj K.obj)
      L.obj))
    (hUV : IsIso (supportedExteriorProduct A (i.openComplement.ι ≫ f)
      (j.openComplement.ι ≫ g) (𝟙 i.openComplement.toScheme)
      (𝟙 j.openComplement.toScheme)
      ((upperStar (ModuleCat.{u + 1} A) i.openComplement.ι).mapDerivedCategory.obj K.obj)
      ((upperStar (ModuleCat.{u + 1} A) j.openComplement.ι).mapDerivedCategory.obj
        L.obj))) :
    IsIso (supportedExteriorProduct A f g i j K.obj L.obj) := by
  have hXW := isIso_second_localization k A f g j K L hF hXY hXV
  let KU := (upperStar (ModuleCat.{u + 1} A) i.openComplement.ι).mapDerivedCategoryPlus.obj K
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have hFU : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) (i.openComplement.ι ≫ f) g KU.obj L.obj).IsGE n := by
    obtain ⟨n, hn⟩ := hF
    have := hn
    have := (upperStar (ModuleCat.{u + 1} A)
      (supportedFirstOpenMap f g i.openComplement)).isGE_mapDerivedCategory_obj
        (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj) n
    exact ⟨n, DerivedCategory.TStructure.t.isGE_of_iso
      (supportedFirstExternalOpenIso (ModuleCat.{u + 1} A) f g i.openComplement K.obj L.obj) n⟩
  have hUW := isIso_second_localization k A (i.openComplement.ι ≫ f) g j KU L
    hFU hUY hUV
  obtain ⟨hS, hT, m, hm₁, hm₂, hm₃⟩ :=
    supportedProductLocalizationFirst k A f g (𝟙 X) i j K L hF
  have h₂ : IsIso m.hom₂ := by
    simpa only [hm₂, supportedFirstLocalizationComponent₂] using hXW
  have hOpen : IsIso (supportedExteriorProduct A (i.openComplement.ι ≫ f) g
      (supportOnOpen (𝟙 X) i.openComplement) j KU.obj L.obj) :=
    (isIso_product_support_congr A _ _ (supportOnOpen (𝟙 X) i.openComplement)
      (𝟙 i.openComplement.toScheme) j j (onOpen_id_complement X i.openComplement)
      rfl _ _).2 hUW
  have h₃ : IsIso m.hom₃ := by
    rw [hm₃]
    dsimp only [supportedFirstLocalizationComponent₃]
    apply (isIso_comp_right_iff _ _).2
    exact hOpen
  have h₁ := isIso₁_of_isIso₂₃ m hS hT h₂ h₃
  rw [hm₁] at h₁
  dsimp only [supportedFirstLocalizationComponent₁] at h₁
  have hi : IsIso (supportedExteriorProduct A f g
      (supportIntersection (𝟙 X) i) j K.obj L.obj) :=
    (isIso_comp_right_iff _ _).1 h₁
  exact (isIso_product_support_congr A f g (supportIntersection (𝟙 X) i) i j j
    (intersection_id_complement i) rfl _ _).1 hi

end AlgebraicGeometry.Etale
