/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.AB
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.Algebra.Homology.KInjectiveProducts
import Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence

/-! # Derived sections over a site object and derived inverse limits

Source: Stacks Project, Cohomology on Sites, Lemma 0D6K, first assertion;
Injectives, Lemma 08U1 (blueprint: lem-kun-site-rgamma-derived-limit).

The helper declarations supply the K-injective structure from the recorded existence
node and define the section functor and its unbounded right derived functor.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w w'

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Transport abelian sheafification from the small model of the site. This is
Mathlib's existing sheafification transport, with the coefficient universe specified.
Source: Stacks Project, Sites, Section 00ZG; Mathlib, Sites/Equivalence,
transport from an equivalent small site
(blueprint: lem-kun-site-rgamma-derived-limit). -/
noncomputable instance siteAbelianHasSheafify
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{r} C] : HasSheafify J AddCommGrpCat.{r} :=
  hasSheafifyEssentiallySmallSite.{v, r, c, r + 1, r} J AddCommGrpCat.{r}

/-- Transport the characterization of sheafification equivalences by locally
bijective maps from the same small model. No extra site hypothesis is imposed.
Source: Stacks Project, Sites, Section 00ZG; Mathlib, Sites/Equivalence,
transport from an equivalent small site
(blueprint: lem-kun-site-rgamma-derived-limit). -/
noncomputable instance siteAbelianWEqualsLocallyBijective
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{r} C] : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, r, c, r + 1, r, r, r} J

/-- K-injective resolutions for modules on a ringed site, obtained directly from
`prop-pur-kinjective-resolutions-exist`, not imposed as an extra hypothesis.
Source: Stacks Project, Injectives, Theorem 079P
(blueprint: lem-kun-site-rgamma-derived-limit). -/
noncomputable abbrev siteModuleKInjectiveResolutions
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max c v r}) :
    Abelian.HasKInjectiveResolutions (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)) :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J O).1
  Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian

/-- Sections over `U`, with the coefficient action forgotten. This is evaluation of
module sheaves followed by the existing forgetful functor to abelian groups.
Source: Stacks Project, Cohomology on Sites, Lemma 0D6K
(blueprint: lem-kun-site-rgamma-derived-limit). -/
noncomputable abbrev siteModuleSections
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max c v r}) (U : C) :
    ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O) ⥤
      AddCommGrpCat.{max c v r} :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
    (evaluation Cᵒᵖ AddCommGrpCat.{max c v r}).obj (op U)

/-- The unbounded right derived sections functor. On a K-injective complex its
value is the localization of its termwise sections, via
`Functor.rightDerivedFunctorObjQIso`. The resolution structure above supplies its existence
from the recorded resolution node, and the shift isomorphism is the canonical
one on the unbounded right derived functor.
Source: Stacks Project, Cohomology on Sites, Lemma 0D6K
(blueprint: lem-kun-site-rgamma-derived-limit). -/
noncomputable abbrev siteModuleDerivedSections
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max c v r}) (U : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))]
    [HasDerivedCategory.{w'} AddCommGrpCat.{max c v r}] :=
  letI := siteModuleKInjectiveResolutions.{c, v, r} J O
  (siteModuleSections.{c, v, r} J O U).rightDerivedFunctor

/-- Sections over any object of a small ringed site preserve derived products and
send a specified derived-limit triangle to its image tower's derived-limit triangle.
The comparison respects every product projection and therefore also the induced
projections from the derived limit.

Source: Stacks Project, Cohomology on Sites, Lemma 0D6K, first assertion
(blueprint: lem-kun-site-rgamma-derived-limit).

Proof:
1. Sections are additive, being evaluation of the underlying abelian presheaf.
   The recorded small-site K-injective existence theorem supplies resolutions.
   The right derived functor is computed by sections of K-injective models;
   `lem-weil-pbc-kinjective-hom-derived` identifies maps with homotopy classes,
   and applying sections to a homotopy shows compatibility with these maps.
2. Choose K-injective representatives of all tower terms. Their degreewise
   product exists by `lem-weil-pbc-module-sheaves-limits-sectionwise` and is
   K-injective and a derived product by `lem-pc-ringed-space-product-kinjective`.
   Its unique product comparison with the prescribed product respects projections.
3. Sections of this complex are the degreewise product of sections. Products
   of abelian groups are exact (`lem-pc-abelian-groups-exact-products`), so
   `lem-weil-derived-limit-existence`, clause (2), identifies its localization
   with the product in the target derived category. The K-injective comparisons
   and the source product comparison give `e` with the displayed equations.
4. The right derived functor is triangulated by
   `lem-pc-right-derived-functor-triangulated`. Additivity and the equations for
   `e` identify the image of `1-s` with the target `1-s` after every projection.
   Transport the distinguished triangle along `e` at both product vertices.
   Its last arrow is `e.inv` followed by the image of `δ` and the shift comparison.
   This is a derived-limit triangle by `def-weil-derived-limit`, and composing
   the projection equations with the image of `p` gives the final clause. -/
theorem site_rgamma_derivedLimit
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{max c v r}) (U : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O))]
    [HasDerivedCategory.{w'} AddCommGrpCat.{max c v r}]
    (K : ℕ → DerivedCategory (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)))
    [HasProduct K]
    (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
    (L : DerivedCategory (ringedSiteModules.{max c v r, max c v r, v, c}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj O)))
    (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (hK : IsDerivedLimitTriangle f L p δ) :
    ∃ e : (siteModuleDerivedSections.{c, v, r, w, w'} J O U).obj (∏ᶜ K) ≅
        ∏ᶜ (fun n : ℕ ↦ (siteModuleDerivedSections.{c, v, r, w, w'} J O U).obj (K n)),
      (∀ n : ℕ, e.hom ≫ Pi.π _ n =
        (siteModuleDerivedSections.{c, v, r, w, w'} J O U).map (Pi.π K n)) ∧
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (siteModuleDerivedSections.{c, v, r, w, w'} J O U).map (f n))
        ((siteModuleDerivedSections.{c, v, r, w, w'} J O U).obj L)
        ((siteModuleDerivedSections.{c, v, r, w, w'} J O U).map p ≫ e.hom)
        (e.inv ≫ (siteModuleDerivedSections.{c, v, r, w, w'} J O U).map δ ≫
          ((siteModuleDerivedSections.{c, v, r, w, w'} J O U).commShiftIso (1 : ℤ)).hom.app L) ∧
      (∀ n : ℕ, (siteModuleDerivedSections.{c, v, r, w, w'} J O U).map p ≫ e.hom ≫ Pi.π _ n =
        (siteModuleDerivedSections.{c, v, r, w, w'} J O U).map (p ≫ Pi.π K n)) := by
  sorry

end CategoryTheory
