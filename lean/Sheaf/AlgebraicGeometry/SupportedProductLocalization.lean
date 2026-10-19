/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.DerivedCategories

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.TensorPullback
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Topology.InverseImageModule
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Topology.Sheaves.Functors
import WeilConjectures.AlgebraicGeometry.Picard.Defs
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import Sheaf.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Sheaf.Paper.EtaleKFlatCriteria
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.AlgebraicGeometry.SupportRestrictionTriangle
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.GlobalSectionsStalkComparison
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import Sheaf.Paper.ExternalRHomConePairing
import Sheaf.SixFunctors.OpenClosedFlatness
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Supported exterior products and localization triangles

Source: Stacks Tags 09XP and 0F1E, and the refinement in the complete proof of
lem-pur-supported-product-localization (blueprint: lem-pur-supported-product-localization).
The third components are the supported exterior products on the actual open product
schemes, transported through the canonical ambient and coefficient comparisons.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- The support triangle tensored in the first variable, using the canonical
exact tensor functor and its signed shift comparison.
Source: Tag 09XP (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationSource (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (_f : X ⟶ S) (_g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  (tensorRight ((supportedSectionsDerived A d).obj L)).mapTriangle.obj
    (normalizedSupportTriangle A b c K)

/-- The product support triangle, with the normalized injective-resolution boundary.
Source: Tag 09XP (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationTarget (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  normalizedSupportTriangle A (supportedProductImmersion f g b d) (supportedProductImmersion f g
    c (𝟙 Y))
    (externalProduct (ModuleCat.{u + 1} A) f g K L)

/-- The first specified supported exterior-product component.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationComponent₁ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstLocalizationSource A f g b c d K L).obj₁ ⟶
      (supportedFirstLocalizationTarget A f g b c d K L).obj₁ :=
  supportedExteriorProduct A f g (supportIntersection b c) d K L ≫
    (derivedSupportCongruence A (supportedProductImmersion f g (supportIntersection b c) d)
      (supportIntersection (supportedProductImmersion f g b d) (supportedProductImmersion f g c
        (𝟙 Y)))
      (supportedFirstIntersection_complement f g b c d)).hom.app
        (externalProduct (ModuleCat.{u + 1} A) f g K L)

/-- The second specified supported exterior-product component.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationComponent₂ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstLocalizationSource A f g b c d K L).obj₂ ⟶
      (supportedFirstLocalizationTarget A f g b c d K L).obj₂ :=
  supportedExteriorProduct A f g b d K L

/-- The third component is the prescribed supported exterior product on the open
product, transported back by the canonical ambient comparison.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedFirstLocalizationComponent₃ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedFirstLocalizationSource A f g b c d K L).obj₃ ⟶
      (supportedFirstLocalizationTarget A f g b c d K L).obj₃ :=
  supportedExteriorProduct A (c.openComplement.ι ≫ f) g
      (supportOnOpen b c.openComplement) d
      ((upperStar (ModuleCat.{u + 1} A) c.openComplement.ι).mapDerivedCategory.obj K) L ≫
    (supportedFirstLocalizationThirdIso A f g b c d K L).inv

/-- The three specified supported exterior products form a morphism of distinguished
localization triangles in the first variable. The third morphism equation in
`TriangleMorphism` includes the connecting maps and the canonical tensor shift iso.
For the first variable that iso has no additional sign on homogeneous tensors; for the
second variable it is multiplication by (-1) to the degree of the first tensor factor.
No component is asserted invertible.

Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
Proof plan:
1. Identify the product and intersection supports on affine product charts by sums of
   extended ideals; identify the product open with the complement of the cut support.
2. Apply the exact K-flat right tensor functor to the support restriction triangle,
   using lem-pc-derived-tensor-second-factor-functor.
3. Use a bounded-below injective representative and the open-closed coefficient sequence
   to identify supported sections with Hom from the closed supported constant sheaf.
4. Apply the open-closed coefficient sequence to the support sheaf of B. Its three
   coefficient terms are flat on geometric stalks. Their external tensors are exactly
   the corresponding three product support coefficient sheaves.
5. Pull back and tensor the two evaluation maps. The adjoint pairing on Hom complexes
   has formula (e tensor d) maps to (-1)^(degree(g) degree(e)) f(e) tensor g(d).
   Naturality under precomposition checks both cone summands and the off-diagonal entry,
   so this is the prescribed third pairing as well as the first two pairings.
6. Apply Hom into injectives to the two coefficient sequences. The degreewise short
   exact sequences compute the two support triangles. The normalized boundaries are
   their actual short-exact-complex connecting maps.
7. The total differential is d tensor 1 + (-1)^p 1 tensor d. Its shift comparisons give
   respectively no extra sign and (-1)^p; these are the imported tensor CommShift maps.
8. For the second variable repeat the coefficient-sequence argument in that variable.
   Pullback, evaluation and restriction commute with coefficient morphisms and open
   restrictions; hence all three squares are natural in both senses. -/
theorem supportedProductLocalizationFirst (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y B C D : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (b : B ⟶ X) (c : C ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hF : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE n) :
    supportedFirstLocalizationSource A f g b c d K.obj L.obj ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} A)) ∧
      supportedFirstLocalizationTarget A f g b c d K.obj L.obj ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} A)) ∧
      ∃ m : supportedFirstLocalizationSource A f g b c d K.obj L.obj ⟶
          supportedFirstLocalizationTarget A f g b c d K.obj L.obj,
        m.hom₁ = supportedFirstLocalizationComponent₁ A f g b c d K.obj L.obj ∧
        m.hom₂ = supportedFirstLocalizationComponent₂ A f g b c d K.obj L.obj ∧
        m.hom₃ = supportedFirstLocalizationComponent₃ A f g b c d K.obj L.obj := by
  sorry

/-- The support triangle tensored in the second variable, using the canonical
exact tensor functor and its signed shift comparison.
Source: Tag 09XP (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationSource (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (_f : X ⟶ S) (_g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  (tensorLeft ((supportedSectionsDerived A b).obj K)).mapTriangle.obj (normalizedSupportTriangle
    A d c L)

/-- The product support triangle, with the normalized injective-resolution boundary.
Source: Tag 09XP (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationTarget (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    Triangle (DerivedCategory (ModuleCat.{u + 1} A)) :=
  normalizedSupportTriangle A (supportedProductImmersion f g b d) (supportedProductImmersion f g
    (𝟙 X) c)
    (externalProduct (ModuleCat.{u + 1} A) f g K L)

/-- The first specified supported exterior-product component.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationComponent₁ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondLocalizationSource A f g b c d K L).obj₁ ⟶
      (supportedSecondLocalizationTarget A f g b c d K L).obj₁ :=
  supportedExteriorProduct A f g b (supportIntersection d c) K L ≫
    (derivedSupportCongruence A (supportedProductImmersion f g b (supportIntersection d c))
      (supportIntersection (supportedProductImmersion f g b d) (supportedProductImmersion f g (𝟙
        X) c))
      (supportedSecondIntersection_complement f g b c d)).hom.app
        (externalProduct (ModuleCat.{u + 1} A) f g K L)

/-- The second specified supported exterior-product component.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationComponent₂ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondLocalizationSource A f g b c d K L).obj₂ ⟶
      (supportedSecondLocalizationTarget A f g b c d K L).obj₂ :=
  supportedExteriorProduct A f g b d K L

/-- The third component is the prescribed supported exterior product on the open
product, transported back by the canonical ambient comparison.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedSecondLocalizationComponent₃ (A : Type (u + 1)) [CommRing A]
    {S X Y B C D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    (supportedSecondLocalizationSource A f g b c d K L).obj₃ ⟶
      (supportedSecondLocalizationTarget A f g b c d K L).obj₃ :=
  supportedExteriorProduct A f (c.openComplement.ι ≫ g)
      b (supportOnOpen d c.openComplement) K
      ((upperStar (ModuleCat.{u + 1} A) c.openComplement.ι).mapDerivedCategory.obj L) ≫
    (supportedSecondLocalizationThirdIso A f g b c d K L).inv

/-- The three specified supported exterior products form a morphism of distinguished
localization triangles in the second variable. The third morphism equation in
`TriangleMorphism` includes the connecting maps and the canonical tensor shift iso.
For the first variable that iso has no additional sign on homogeneous tensors; for the
second variable it is multiplication by (-1) to the degree of the first tensor factor.
No component is asserted invertible.

Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
Proof plan:
1. Identify the product and intersection supports on affine product charts by sums of
   extended ideals; identify the product open with the complement of the cut support.
2. Apply the exact K-flat right tensor functor to the support restriction triangle,
   using lem-pc-derived-tensor-second-factor-functor.
3. Use a bounded-below injective representative and the open-closed coefficient sequence
   to identify supported sections with Hom from the closed supported constant sheaf.
4. Apply the open-closed coefficient sequence to the support sheaf of B. Its three
   coefficient terms are flat on geometric stalks. Their external tensors are exactly
   the corresponding three product support coefficient sheaves.
5. Pull back and tensor the two evaluation maps. The adjoint pairing on Hom complexes
   has formula (e tensor d) maps to (-1)^(degree(g) degree(e)) f(e) tensor g(d).
   Naturality under precomposition checks both cone summands and the off-diagonal entry,
   so this is the prescribed third pairing as well as the first two pairings.
6. Apply Hom into injectives to the two coefficient sequences. The degreewise short
   exact sequences compute the two support triangles. The normalized boundaries are
   their actual short-exact-complex connecting maps.
7. The total differential is d tensor 1 + (-1)^p 1 tensor d. Its shift comparisons give
   respectively no extra sign and (-1)^p; these are the imported tensor CommShift maps.
8. For the second variable repeat the coefficient-sequence argument in that variable.
   Pullback, evaluation and restriction commute with coefficient morphisms and open
   restrictions; hence all three squares are natural in both senses. -/
theorem supportedProductLocalizationSecond (k : Type u) [Field k] [IsAlgClosed k]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y B C D : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (b : B ⟶ X) (c : C ⟶ Y) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion c] [IsClosedImmersion d]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hF : ∃ n : ℤ,
      (externalProduct (ModuleCat.{u + 1} A) f g K.obj L.obj).IsGE n) :
    supportedSecondLocalizationSource A f g b c d K.obj L.obj ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} A)) ∧
      supportedSecondLocalizationTarget A f g b c d K.obj L.obj ∈
        distTriang (DerivedCategory (ModuleCat.{u + 1} A)) ∧
      ∃ m : supportedSecondLocalizationSource A f g b c d K.obj L.obj ⟶
          supportedSecondLocalizationTarget A f g b c d K.obj L.obj,
        m.hom₁ = supportedSecondLocalizationComponent₁ A f g b c d K.obj L.obj ∧
        m.hom₂ = supportedSecondLocalizationComponent₂ A f g b c d K.obj L.obj ∧
        m.hom₃ = supportedSecondLocalizationComponent₃ A f g b c d K.obj L.obj := by
  sorry

/-- Map the derived external product in both coefficient objects using its bifunctor.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization). -/
noncomputable def supportedExternalProductMap (A : Type (u + 1)) [CommRing A]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {K K' : DerivedCategoryModule A X} {L L' : DerivedCategoryModule A Y}
    (a : K ⟶ K') (e : L ⟶ L') :
    externalProduct (ModuleCat.{u + 1} A) f g K L ⟶
      externalProduct (ModuleCat.{u + 1} A) f g K' L' :=
  (supportedExternalProductIso (ModuleCat.{u + 1} A) f g K L).hom ≫
    supportedDerivedTensorMap A (pullback f g)
    ((upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map a)
    ((upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.map e) ≫
    (supportedExternalProductIso (ModuleCat.{u + 1} A) f g K' L').inv

/-- Naturality of every specified exterior-product component under coefficient morphisms.
Source: Tag 0F1E (blueprint: lem-pur-supported-product-localization).
Proof: evaluation and the coefficient tensor map are natural in both variables. Apply
that naturality to their composite and then the natural supported-coefficient adjunction.
The argument applies also on each open product, hence to all three triangle components. -/
theorem supportedProductLocalization_naturality (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d]
    {K K' : DerivedCategoryModule A X} {L L' : DerivedCategoryModule A Y}
    (a : K ⟶ K') (e : L ⟶ L') :
    ((supportedSectionsDerived A b).map a ⊗ₘ (supportedSectionsDerived A d).map e) ≫
        supportedExteriorProduct A f g b d K' L' =
      supportedExteriorProduct A f g b d K L ≫
        (supportedSectionsDerived A (supportedProductImmersion f g b d)).map
          (supportedExternalProductMap A f g a e) := by
  sorry

/-- Naturality under open restriction of the first ambient scheme, for every
support, hence for all three components of each localization diagram.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
Proof: the ordinary kernel restriction commutes with pulling back and tensoring sections.
The uniquely normalized coefficient maps preserve this equality on each tensor bidegree.
Use K-flat models, injective support resolutions and their canonical comparisons to derive
that equality. The product-open comparison is exactly the one used in the third component. -/
theorem supportedProductLocalization_openFirst (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    supportedExteriorProduct A f g b d K L ≫
        supportedFirstExternalRestriction A f g b d U K L =
      ((derivedSupportOpenRestriction A b U).app K ⊗ₘ 𝟙 _) ≫
        supportedExteriorProduct A (U.ι ≫ f) g (supportOnOpen b U) d ((upperStar (ModuleCat.{u +
          1} A) U.ι).mapDerivedCategory.obj K) L := by
  sorry

/-- Naturality under open restriction of the second ambient scheme, for every
support, hence for all three components of each localization diagram.
Source: Tags 09XP and 0F1E (blueprint: lem-pur-supported-product-localization).
Proof: the ordinary kernel restriction commutes with pulling back and tensoring sections.
The uniquely normalized coefficient maps preserve this equality on each tensor bidegree.
Use K-flat models, injective support resolutions and their canonical comparisons to derive
that equality. The product-open comparison is exactly the one used in the third component. -/
theorem supportedProductLocalization_openSecond (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (V : Y.Opens)
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    supportedExteriorProduct A f g b d K L ≫
        supportedSecondExternalRestriction A f g b d V K L =
      (𝟙 _ ⊗ₘ (derivedSupportOpenRestriction A d V).app L) ≫
        supportedExteriorProduct A f (V.ι ≫ g) b (supportOnOpen d V) K ((upperStar (ModuleCat.{u
          + 1} A) V.ι).mapDerivedCategory.obj L) := by
  sorry

/-- The support localization rows themselves are natural under open restriction,
including their connecting maps. The three components are the canonical restrictions,
with the third coefficient comparison fixed by the commuting square of cut complements.
Together with supportedProductLocalization_openFirst and _openSecond this gives
naturality of the complete exterior-product diagrams, rather than just their pairings.
Source: Tags 09XP and 0F1E; proof step 9 of the node
(blueprint: lem-pur-supported-product-localization).
Proof: restrict a termwise injective K-injective representative to the open immersion.
Exact extension by zero is left adjoint to restriction, so restriction preserves both
injective objects and K-injectivity. Ordinary support restrictions give a morphism
between the two degreewise short exact support sequences. Naturality of triangleOfSESδ
makes its boundary square commute. The unique boundary normalization and canonical
right-derived composition units identify all three components with the displayed maps.
Apply this on X, on Y, and on the product open to obtain the row restriction morphisms.
The exterior-product restriction identities identify the three squares between rows. -/
theorem supportedProductLocalization_openRows (A : Type (u + 1)) [CommRing A]
    {T S B C B' C' : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (c : C ⟶ T) (b' : B' ⟶ S) (c' : C' ⟶ S)
    [IsClosedImmersion b] [IsClosedImmersion c]
    [IsClosedImmersion b'] [IsClosedImmersion c']
    (hb : b'.openComplement = h ⁻¹ᵁ b.openComplement)
    (hc : c'.openComplement = h ⁻¹ᵁ c.openComplement)
    (K : DerivedCategoryModule A T) :
    ∃ m : normalizedSupportTriangle A b c K ⟶
        normalizedSupportTriangle A b' c'
          ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj K),
      m.hom₁ = (derivedSupportTransport A h (supportIntersection b c)
        (supportIntersection b' c')
        (supportRestrictedIntersection_complement h b c b' c' hb hc)).app K ∧
      m.hom₂ = (derivedSupportTransport A h b b' hb).app K ∧
      m.hom₃ = supportTriangleRestrictionThird A h b c b' c' hb hc K := by
  sorry

end AlgebraicGeometry.Etale
