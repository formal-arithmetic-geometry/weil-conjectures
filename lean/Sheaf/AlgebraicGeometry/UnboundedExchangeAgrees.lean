/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import Mathlib
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Unbounded exchange agrees with bounded exchange and with degree-zero exchange

Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node lem-kun-unbounded-exchange-agrees; Stacks Project, Tags 07A7 and 05TD(3)
(blueprint: lem-kun-unbounded-exchange-agrees).

The endpoint isomorphisms below are composites of the fixed exact-functor cohomology
comparison, the single-object right-derived comparison, and the degree-zero comparison.
The last two are induced by augmentations into nonnegative injective resolutions.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical source identification in degree zero, induced by the augmentation.
Source: Stacks Project, Tag 05TD(3), and exact inverse image, Tag 0735
(blueprint: lem-kun-unbounded-exchange-agrees). -/
noncomputable def exchangeSourceZeroIso
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (F : Sheaf X.smallEtaleTopology A) :
    (_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((D((g)^*[A])).obj ((R((f)_*[A])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≅
      ((g)^*[A]).obj (((f)_*[A]).obj F) :=
  (((g)^*[A]).mapDerivedCategoryHomologyFunctorIso 0).symm.app _ ≪≫
    ((g)^*[A]).mapIso
      (((f)_*[A]).homologyRightDerivedFunctorObjSingleFunctorIso F 0 ≪≫
        ((f)_*[A]).rightDerivedZeroIsoSelf.app F)

/-- The canonical target identification in degree zero, induced by the augmentation.
Source: Stacks Project, Tag 05TD(3), and exact inverse image, Tag 0735
(blueprint: lem-kun-unbounded-exchange-agrees). -/
noncomputable def exchangeTargetZeroIso
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (F : Sheaf X.smallEtaleTopology A) :
    (_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((R((f')_*[A])).obj ((D((g')^*[A])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≅
      ((f')_*[A]).obj (((g')^*[A]).obj F) :=
  (_root_.DerivedCategory.homologyFunctor _ 0).mapIso
      ((R((f')_*[A])).mapIso ((((g')^*[A]).mapDerivedCategorySingleFunctor 0).app F)) ≪≫
    ((f')_*[A]).homologyRightDerivedFunctorObjSingleFunctorIso (((g')^*[A]).obj F) 0 ≪≫
    ((f')_*[A]).rightDerivedZeroIsoSelf.app (((g')^*[A]).obj F)

/-- At integral (abelian) coefficients the unbounded exchange restricts to the bounded
below exchange, under the canonical direct-image and inverse-image comparisons.
Source: blueprint lem-kun-unbounded-exchange-agrees, first paragraph; Stacks, Tag 07A7
(blueprint: lem-kun-unbounded-exchange-agrees).

Proof: Choose a bounded below injective representative I of K. It is K-injective
(lem-weil-pbc-dplus-injective-representative), so both direct images are represented by
u_* I. Uniqueness of right derivation with its unit gives the fixed natural comparison
rightDerivedFunctorPlusCompatibility (lem-weil-pbc-kinjective-total-derived and
lem-weil-pbc-kinjective-hom-derived). Inverse image is the same exact termwise functor
(def-weil-pbc-derived-inverse-image). The termwise adjunction and the derived Hom
bijection into a K-injective identify both units and counits in the two models
(lem-weil-pbc-termwise-adjunction-homotopy, lem-pc-derived-adjoint-functors,
prop-weil-pbc-derived-inverse-image-adjunction). Both square maps are the localized
termwise squareUpperStarIso. Therefore their transposes are the same square map
followed by inverse image of the same counit. Injectivity of the adjunction bijection
(def-weil-pbc-adjunction-mate) identifies the exchanges. -/
theorem exactDerivedBaseChangeMap_agrees_plus
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app K.obj =
      (D((g)^*[AddCommGrpCat.{u + 1}])).map
        (((f)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
      _root_.DerivedCategory.Plus.ι.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) ≫
      ((f')_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlusCompatibility.hom.app
        ((D+((g')^*[AddCommGrpCat.{u + 1}])).obj K) := by
  sorry

/-- On a sheaf in degree zero, the zeroth cohomology of the unbounded module exchange
is the module mate; after the fixed coefficient comparisons its underlying abelian map
is the underived abelian exchange.
Source: blueprint lem-kun-unbounded-exchange-agrees, second paragraph; Stacks, Tags 07A7
and 05TD(3) (blueprint: lem-kun-unbounded-exchange-agrees).

Proof: Choose nonnegative injective resolutions s:F[0] → I and t:g'⁻¹F[0] → J
(lem-weil-pbc-module-sheaves-enough-injectives). Both are K-injective. Exactness of
inverse image makes g'⁻¹s a quasi-isomorphism. The K-injective Hom bijection gives a
chain map j:g'⁻¹I → J with j g'⁻¹s = t: a possible homotopy has its only component
in J⁻¹ = 0. Apply the module underived mate termwise and then f'_*j to obtain e.
Naturality of the counit and the defining mate identity show that Qe has the same
transpose as exactDerivedBaseChangeMap, hence represents it. Naturality of the module
mate gives e g⁻¹f_*s = f'_*t Ex⁰_F. Left exactness of f_* and f'_* identifies the
zeroth homology of their augmentations with their ordinary direct images
(lem-weil-pbc-left-exact-injective-resolution-degree-zero). Exact inverse image respects
this augmentation comparison (lem-weil-pbc-exact-functor-complex-cohomology). Taking
zeroth homology therefore gives the first equality with precisely the two displayed
canonical endpoint isomorphisms. Finally apply
lem-weil-pbc-module-abelian-underived-exchange to that module mate, inserting the fixed
inverse-image coefficient comparisons and direct-image evaluation identities. This gives
the second equality. This argument asserts no equality in higher degrees. -/
theorem exactDerivedBaseChangeMap_homology_zero
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (_root_.DerivedCategory.homologyFunctor _ 0).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
        (exchangeTargetZeroIso (ModuleCat.{u + 1} Λ) g' f' F).hom =
      (exchangeSourceZeroIso (ModuleCat.{u + 1} Λ) f g F).hom ≫
        (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F ∧
    (moduleAbelianForget Λ Y').map
        ((exchangeSourceZeroIso (ModuleCat.{u + 1} Λ) f g F).inv ≫
          (_root_.DerivedCategory.homologyFunctor _ 0).map
            ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
              ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
          (exchangeTargetZeroIso (ModuleCat.{u + 1} Λ) g' f' F).hom) ≫
        (moduleAbelianLowerStarIso Λ f').hom.app (((g')^*[ModuleCat.{u + 1} Λ]).obj F) ≫
        ((f')_*[AddCommGrpCat.{u + 1}]).map ((moduleAbelianUpperStarIso Λ g').inv.app F) =
      (moduleAbelianUpperStarIso Λ g).inv.app (((f)_*[ModuleCat.{u + 1} Λ]).obj F) ≫
        ((g)^*[AddCommGrpCat.{u + 1}]).map ((moduleAbelianLowerStarIso Λ f).hom.app F) ≫
        (baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
          ((moduleAbelianForget Λ X).obj F) := by
  sorry

end AlgebraicGeometry.Etale
