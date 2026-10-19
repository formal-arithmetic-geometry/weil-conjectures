/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Restriction triangle inside a closed support

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
lem-pur-support-restriction-triangle.md, statement and all six proof steps.
(blueprint: lem-pur-support-restriction-triangle).

The first two arrows are specified by their underlying section maps, not by arbitrary
morphisms between the three derived objects. The third support is a closed subset of
`V = T \ C`, and its section functor and derived category are formed on `V` itself.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- For closed immersions `b : B ⟶ T` and `c : C ⟶ T`, there is a natural distinguished
triangle of derived supported sections, with supports `B ∩ C`, `B`, and `B ∩ V` on
`V = T \ C`. The inclusion `a` and restriction `r` are characterized by their composites
with the monic inclusions into global sections. The comparison `e` is characterized by
the units of the right derived functors; hence it identifies the derived composite with
`RΓ` on `V` after the exact inverse image `v*`, without choosing an arbitrary isomorphism.
Naturality of the connecting map is expressed by the natural transformation `δ`.

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer,
lem-pur-support-restriction-triangle, statement and proof.
(blueprint: lem-pur-support-restriction-triangle).

Proof plan:
1. Sections supported on a closed subset are the kernel of restriction to its complement,
   an additive left exact functor. Use lem-weil-pbc-module-sheaves-enough-injectives and
   lem-weil-pbc-dplus-injective-representative to represent each bounded below object by
   bounded below injectives. Restriction to an open is exact and preserves injectives by
   prop-weil-pbc-inverse-image-modules-exact and lem-weil-pbc-etale-restriction-injectives;
   lem-weil-pbc-open-immersion-etale applies to the open complement.
2. Put `W = T \ B`, `V = T \ C`, and `O = V ∪ W`. The counit monomorphism for extension
   by zero of the rank-one constant module on `O`, from lem-weil-pbc-open-closed-short-exact,
   makes `J(T) → J(O)` onto for injective `J`. Use def-sp-injective-resolutions and
   lem-weil-pbc-extension-by-zero-adjunction to identify the lifting map with restriction.
3. A section on `V` supported on `B ∩ V` is zero on `V ∩ W`. Glue it to zero on `W`, using
   def-weil-pbc-abelian-etale-sheaves and def-weil-sheaf-of-modules-category. Lift the glued
   section on `O` to `T` by step 2. It is zero on `W`, hence supported on `B`.
4. The kernel of this supported restriction consists of sections zero on `V` and `W`,
   equivalently on `O`; it is exactly the sections supported on `B ∩ C`. Apply degreewise
   to the injective complex. Inclusions and restrictions commute with differentials and
   chain maps, giving the natural short exact sequence of section complexes.
5. Use lem-weil-pbc-right-derived-plus-injective on `T` and on `V` to identify all three
   complexes with the displayed derived functors. The complement of `B ∩ V` in `V` is
   `v⁻¹(W)`, so the third functor is genuinely on `V`. The unit characterization gives
   `e`. Apply lem-weil-pbc-complex-ses-triangle to obtain the distinguished triangle.
6. Represent derived morphisms by chain maps of bounded below injective representatives,
   using lem-weil-pbc-kinjective-hom-derived and K-injectivity from step 1. Naturality of
   the short exact complex triangle gives the connecting map. Additive section functors
   preserve homotopies, so the maps descend to the derived category and are independent
   of resolutions. This gives the natural transformation `δ`. -/
theorem supportRestrictionTriangle (R : Type (u + 1)) [CommRing R]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c] :
    ∃ (a : supportedEtaleSections R T (b.openComplement ⊔ c.openComplement) ⟶
        supportedEtaleSections R T b.openComplement)
      (r : supportedEtaleSections R T b.openComplement ⟶
        upperStar (ModuleCat.{u + 1} R) c.openComplement.ι ⋙
          supportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement))
      (e : (upperStar (ModuleCat.{u + 1} R) c.openComplement.ι ⋙
          supportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement)).rightDerivedFunctorPlus ≅
        (upperStar (ModuleCat.{u + 1} R) c.openComplement.ι).mapDerivedCategoryPlus ⋙
          (supportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement)).rightDerivedFunctorPlus)
      (δ : (upperStar (ModuleCat.{u + 1} R) c.openComplement.ι).mapDerivedCategoryPlus ⋙
          derivedSupportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement) ⟶
        derivedSupportedEtaleSections R T (b.openComplement ⊔ c.openComplement) ⋙
          shiftFunctor (DerivedCategory (ModuleCat.{u + 1} R)) (1 : ℤ)),
      (∀ M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R),
        a.app M ≫ (supportedEtaleSectionsι R T b.openComplement).app M =
          (supportedEtaleSectionsι R T (b.openComplement ⊔ c.openComplement)).app M) ∧
      (∀ M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R),
        r.app M ≫ (supportedEtaleSectionsι R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement)).app
              ((upperStar (ModuleCat.{u + 1} R) c.openComplement.ι).obj M) =
          (supportedEtaleSectionsι R T b.openComplement).app M ≫
            globalSectionsUpperStarMap (ModuleCat.{u + 1} R) c.openComplement.ι M) ∧
      ((upperStar (ModuleCat.{u + 1} R) c.openComplement.ι ⋙
          supportedEtaleSections R c.openComplement
            (c.openComplement.ι ⁻¹ᵁ b.openComplement)).rightDerivedFunctorPlusUnit ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh e.hom =
        Functor.rightDerivedFunctorPlusCompUnit
            (upperStar (ModuleCat.{u + 1} R) c.openComplement.ι)
            (supportedEtaleSections R c.openComplement
              (c.openComplement.ι ⁻¹ᵁ b.openComplement)) ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh
            (Functor.whiskerRight
              (upperStar (ModuleCat.{u + 1} R)
                c.openComplement.ι).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
              (supportedEtaleSections R c.openComplement
                (c.openComplement.ι ⁻¹ᵁ b.openComplement)).rightDerivedFunctorPlus)) ∧
      ∀ F : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)),
        Triangle.mk
          (DerivedCategory.Plus.ι.map ((Functor.rightDerivedFunctorPlusNatTrans a).app F))
          (DerivedCategory.Plus.ι.map
            ((Functor.rightDerivedFunctorPlusNatTrans r).app F ≫ e.hom.app F))
          (δ.app F) ∈ distTriang (DerivedCategory (ModuleCat.{u + 1} R)) := by
  sorry

end AlgebraicGeometry.Etale
