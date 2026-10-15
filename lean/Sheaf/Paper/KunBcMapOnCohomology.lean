/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Sheaf.AlgebraicGeometry.DerivedExchangeTermwise
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.KInjectiveResolutions

/-!
# Cohomology of the derived base-change map

Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary, order 1752;
Stacks Project, sites-cohomology.tex, Tags 0736 and 07A7
(blueprint: lem-kun-bc-map-on-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Etale

/-- On a sheaf placed in degree zero, the cohomology of derived exchange is the
usual resolution base-change map. The displayed right side writes out that recipe:
compare the direct image of an injective representative `I` with the derived direct
image using its unit and `s`; apply the underived exchange termwise; apply `f'_*`
to the comparison `j` with the injective representative `J`; finally use the derived
unit and the inverse of the pulled-back resolution to identify the target.
Thus applying cohomology implements the quotient of cycles by boundaries, without
requiring global cycle representatives of sections of the quotient sheaf.
The final clause states vanishing of both higher direct images in negative degrees.

Proof:
1. Choose injective representatives of `F[0]` and of its inverse image. Exactness of
inverse image preserves the resolution quasi-isomorphism (inverse-image-exact and
exact-functor-complex-cohomology). In particular, `j` is a comparison with a new
resolution; no injectivity of inverse image of `I` is assumed.
2. The termwise comparison lemma (derived-exchange-termwise) identifies derived
exchange with the underived exchange followed by `f'_*(j)`, conjugated by the
canonical resolution comparisons written here.
3. Apply degree-`q` cohomology to that equation. Exact-functor-complex-cohomology,
via `mapDerivedCategoryPlusHomologyFunctorIso`, identifies the source cohomology
with inverse image of the higher direct image; direct-image defines the target as
the cohomology of the derived direct image. These comparisons are canonical.
4. The chain-map formula takes a cycle class to the class of its termwise
underived exchange followed by `f'_*(j)`. It preserves boundaries, so induces the
usual quotient-sheaf map. For negative `q`, use nonnegative injective representatives
(dplus-injective-representative); additive direct image leaves their negative terms
zero. Consequently both cohomology sheaves vanish.
Source: Stacks Project, Tags 0736 and 07A7; blueprint order 1752
(blueprint: lem-kun-bc-map-on-cohomology). -/
theorem derivedBaseChangeMapPlus_cohomology_resolution
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ) :
    (∀ (I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (J : HomotopyCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}))
      (_ : ∀ n : ℤ, Injective (I.obj.as.X n))
      (_ : ∀ n : ℤ, Injective (J.obj.as.X n))
      (s : ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F) ≅
          DerivedCategory.Plus.Qh.obj I)
      (j : ((g')^*[AddCommGrpCat.{u + 1}]).mapHomotopyCategoryPlus.obj I ⟶ J),
      ∀ [IsIso (DerivedCategory.Plus.Qh.map j)],
      (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
        ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
      (DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
        q).map
        ((Etale.derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
          0).obj F)) ≫
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
          ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
            ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              F)) =
      (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
        ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ≫
      (DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
        q).map
        (inv (((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map
          ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlusUnit.app I ≫
          (f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map s.inv)) ≫
        ((g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusFactorsh.hom.app
          ((f)_*[AddCommGrpCat.{u + 1}].mapHomotopyCategoryPlus.obj I) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus
            (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)).app I) ≫
        DerivedCategory.Plus.Qh.map ((f')_*[AddCommGrpCat.{u + 1}].mapHomotopyCategoryPlus.map j) ≫
        ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlusUnit.app J ≫
          (f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map (inv
            (((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlus.map s.hom ≫
          ((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusFactorsh.hom.app I ≫
          DerivedCategory.Plus.Qh.map j)))) ≫
      (DerivedCategory.Plus.homologyFunctor
        (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) q).map
          ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
            ((((g')^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
              F))) ∧
    (q < 0 →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ∧
      IsZero ((DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology
        AddCommGrpCat.{u + 1}) q).obj
        ((f')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
            (((g')^*[AddCommGrpCat.{u + 1}]).obj F))))) := by
  sorry

end AlgebraicGeometry
