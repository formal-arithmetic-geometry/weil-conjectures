/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF maintenance NZ
-/
module

public import Sheaf.Algebra.Homology.RhomGlobalSections
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
import Sheaf.Algebra.Homology.HomComplexHypercohomology
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-!
# Global sections of derived internal Hom with independent site universes

Source: Stacks Project, Lemma 21.35.1, Tag 08JA, global statement
(blueprint: lem-pur-rhom-global-sections).

This is the same comparison as the publicly imported `rhom_global_sections`, with site
objects, site arrows and coefficient sizes independent. Both operations are the recorded
constructions on the actual site, with module universe `max c v r`.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory Opposite

namespace CategoryTheory

/-- The natural additive identification of zeroth hypercohomology of derived internal Hom
with derived morphisms, without identifying the site object and morphism universes.
The sheafification instances are the canonical abelian-category infrastructure in a
universe containing the site; no flatness, boundedness or product-exactness is assumed.

Source: Stacks Project, Lemma 21.35.1, Tag 08JA, global statement
(blueprint: lem-pur-rhom-global-sections).

Proof:
1. Use the recorded independent-universe K-flat and K-injective resolutions on C.
   For a K-flat representative L and K-injective representative I of M, the sheaf Hom
   complex Hom(L,I) computes derivedInternalHomOfUniverses and is K-injective
   (Tags 0A95 and 0A96). Thus ringedSiteZerothHypercohomologyOfUniverses computes
   its zeroth cohomology by applying Hom_R(R,-) termwise.
2. Sections of degree n of this Hom complex are the families of linear maps
   L^p to I^(p+n), with differential d_I f - (-1)^n f d_L. Its degree-zero cycles
   are chain maps and its boundaries are null-homotopic maps. Consequently H0 is
   the additive group of homotopy classes. For arbitrary source representatives,
   a K-flat resolution and invariance in the first variable transport this comparison;
   common refinements of surjective resolutions show independence and naturality.
3. K-injectivity identifies these homotopy classes with derived morphisms via
   DerivedCategory.Qh.mapAddHom. Compose with quotientCompQhIso and the inverse
   of the localized resolution map. Naturality of that resolution and of the
   quotient comparison gives precomposition by f.1.unop and postcomposition by f.2.
4. Descend this natural additive comparison along Q.op.prod Q using the fully
   faithful whiskering functor for the product localization. ULift places the
   hypercohomology and derived-Hom groups in a common universe; remove those lifts
   from each component to obtain e and the displayed naturality equation.
All products and resolutions are taken in max c v r, which contains the site and
coefficient universes. This changes no section, differential or localization map.
Zero objects and the empty site require no additional hypotheses. -/
theorem rhom_global_sectionsOfUniverses
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :
    ∃ e : ∀ P : (DerivedCategory (SheafOfModules.{max c v r}
        ((sheafCompose J
          (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{max c v r}
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)),
      ((ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R).obj
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj P)) ≃+ (P.1.unop ⟶ P.2),
      ∀ (P P' : (DerivedCategory (SheafOfModules.{max c v r}
          ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))ᵒᵖ ×
          DerivedCategory (SheafOfModules.{max c v r}
            ((sheafCompose J
              (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
        (f : P ⟶ P')
        (x : (ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R).obj
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj P)),
        e P' ((ringedSiteZerothHypercohomologyOfUniverses.{c, v, r, w} J R).map
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map f) x) =
            f.1.unop ≫ e P x ≫ f.2 := by
  sorry

end CategoryTheory
