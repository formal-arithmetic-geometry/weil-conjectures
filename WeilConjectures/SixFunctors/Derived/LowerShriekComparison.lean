/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.SixFunctors.Derived.LowerShriek
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.BaseChange

/-!

# Comparison of derived lower shrieks along a refinement of compactifications

Let `f : X ⟶ Y` be a morphism of schemes, let `c` and `d` be compactifications of `f` and let
`r : c.Refinement d` be a refinement, i.e. a morphism `q = r.hom : c.Z ⟶ d.Z` with
`c.i ≫ q = d.i` and `q ≫ d.g = c.g`. This file constructs the comparison

`Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+`

of the bounded below derived lower shrieks attached to the two compactifications, under the
hypothesis that the square

```
X --c.i--> c.Z
|          |
𝟙          q
|          |
X --d.i--> d.Z
```

is cartesian, i.e. `q ⁻¹ (X) = X`.

Note the direction: the comparison goes from the *coarser* compactification `d` to the
*finer* one `c`. Neither direction is formal — the adjunctions produce a cospan of natural
transformations into `D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*`, and one of the two legs has to be
inverted to obtain an arrow. Inverting the leg coming from the base change comparison for
`j_!` is what the cartesian hypothesis buys, and it produces the direction above; inverting
the other leg is proper base change and produces the opposite direction.

The composite is, with `q = r.hom`:

```
D(d.i)_! ⋙ R(d.g)_*
  ⟶ D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*   (unit of `Dq^* ⊣ Rq_*`)
  ⟶ D(c.i)_! ⋙ Rq_* ⋙ R(d.g)_*          (inverse of base change for `j_!`)
  ⟶ D(c.i)_! ⋙ R(c.g)_*                 (composition of derived pushforwards)
```

## Main definitions

- `AlgebraicGeometry.Etale.refinementLowerStarComp`: the composition isomorphism
  `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards attached to a refinement.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`: the
  comparison `Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+` above. (blueprint: `BA43-RHO`)

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison_id`: the
  identity law, i.e. the comparison attached to the identity refinement of a
  compactification is the identity.

## Implementation notes

Only the bounded below variant is constructed. The unbounded variant would need both the
unbounded derived adjunction `Dq^* ⊣ Rq_*` and the unbounded composition isomorphism for
derived pushforwards, neither of which is available.

That the comparison is an isomorphism is proper base change and is not proved here, nor is
its compatibility with `Compactification.Refinement.comp`.

The identity law is proved by factoring the comparison for the identity refinement through
the whiskering by `D(c.i)_!⁺`: the base change isomorphism for the identity refinement is
the whiskering of the identity isomorphism `D(𝟙 c.Z)^*⁺ ≅ 𝟭` of
`AlgebraicGeometry.Etale.upperStarIdDerivedPlus`
(`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso_inv_id`), which
turns the comparison into a natural transformation of `R(c.g)_*⁺` with itself, and there the
universal property of a right derived functor applies. The two ingredients are that the
derived unit of `D(𝟙 c.Z)^* ⊣ R(𝟙 c.Z)_*` is the inverse of the identity isomorphism
`R(𝟙 c.Z)_*⁺ ≅ 𝟭` of `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus`, and that the
composition isomorphism cancels the latter.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The composition isomorphism `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards on étale
sheaves attached to a refinement `r : c.Refinement d`, coming from
`Etale.lowerStarComp` and the relation `r.hom ≫ d.g = c.g`. -/
noncomputable def refinementLowerStarComp : (r.hom)_*[A] ⋙ (d.g)_*[A] ≅ (c.g)_*[A] :=
  Etale.lowerStarComp A r.hom d.g ≪≫ eqToIso (by rw [r.hom_g])

/-- The base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*` on bounded below derived
categories, induced by `Compactification.Refinement.openImmersionLowerShriekBaseChange` for
a refinement whose square over `X` is cartesian. -/
noncomputable def refinementLowerShriekBaseChangeDerivedPlusIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    (c.i)_!open[A].mapDerivedCategoryPlus ≅
      (d.i)_!open[A].mapDerivedCategoryPlus ⋙ (r.hom)^*[A].mapDerivedCategoryPlus :=
  haveI := r.isIso_openImmersionLowerShriekBaseChange A hcart
  Functor.mapDerivedCategoryPlusNatIso (asIso (r.openImmersionLowerShriekBaseChange A)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The comparison `Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+` of the bounded below derived lower shrieks
attached to two compactifications `c`, `d` of `f : X ⟶ Y` linked by a refinement
`r : c.Refinement d` whose square over `X` is cartesian.

It is the composite of the unit of the derived adjunction
`D(r.hom)^* ⊣ R(r.hom)_*`, the inverse of the base change isomorphism
`D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*`, and the composition isomorphism
`R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`. Note that it goes from the coarser compactification `d`
to the finer one `c`. (blueprint: `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) : Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+ :=
  haveI : ((r.hom)_*[A]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A r.hom)
  Functor.whiskerRight (Functor.whiskerLeft (d.i)_!open[A].mapDerivedCategoryPlus
      (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit)
      (d.g)_*[A].rightDerivedFunctorPlus ≫
    Functor.whiskerRight (refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).inv
      ((r.hom)_*[A].rightDerivedFunctorPlus ⋙ (d.g)_*[A].rightDerivedFunctorPlus) ≫
    Functor.whiskerLeft (c.i)_!open[A].mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusCompIso' (r.hom)_*[A] (d.g)_*[A]
        (refinementLowerStarComp A r)).hom

section IdentityLaw

/-- The comparison isomorphism `Functor.mapDerivedCategoryPlusNatIso` and the composition
isomorphism `Functor.mapDerivedCategoryPlusCompIso` out of which
`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso` is built are both
characterized by their compatibility with the factorizations
`Functor.mapDerivedCategoryPlusFactorsh` through the localization functors; this is the
resulting characterization of the base change isomorphism itself. -/
@[reassoc]
lemma refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).hom.app
          (DerivedCategory.Plus.Qh.obj K) ≫
        ((r.hom)^*[A]).mapDerivedCategoryPlus.map
          (((d.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((d.i)_!open[A]).mapHomotopyCategoryPlus.obj K) =
      ((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (r.openImmersionLowerShriekBaseChange A)).app K) := by
  simp only [refinementLowerShriekBaseChangeDerivedPlusIso, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh]
  rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  simp only [asIso_hom]

variable (V : Scheme.{u})

/-- The identity isomorphism `D(𝟙 V)^*⁺ ≅ 𝟭` of the pullback along the identity on the
bounded below derived categories, induced by `AlgebraicGeometry.Etale.upperStarId`. -/
noncomputable def upperStarIdDerivedPlus :
    ((𝟙 V)^*[A]).mapDerivedCategoryPlus ≅
      𝟭 (DerivedCategory.Plus (Sheaf V.smallEtaleTopology A)) :=
  Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarId A V) ≪≫
    Functor.mapDerivedCategoryPlusIdIso _

/-- On the image of a bounded below complex, `AlgebraicGeometry.Etale.upperStarIdDerivedPlus`
is the factorization `Functor.mapDerivedCategoryPlusFactorsh` followed by the levelwise
image of `AlgebraicGeometry.Etale.upperStarId`. -/
lemma upperStarIdDerivedPlus_hom_app
    (K : HomotopyCategory.Plus (Sheaf V.smallEtaleTopology A)) :
    (upperStarIdDerivedPlus A V).hom.app (DerivedCategory.Plus.Qh.obj K) =
      ((𝟙 V)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K) := by
  rw [upperStarIdDerivedPlus, Iso.trans_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]

/-- The identity isomorphism `R(𝟙 V)_*⁺ ≅ 𝟭` of the pushforward along the identity on the
bounded below derived categories, induced by `AlgebraicGeometry.Etale.lowerStarId`. -/
noncomputable def lowerStarIdDerivedPlus :
    ((𝟙 V)_*[A]).rightDerivedFunctorPlus ≅
      𝟭 (DerivedCategory.Plus (Sheaf V.smallEtaleTopology A)) :=
  Functor.rightDerivedFunctorPlusNatIso (Etale.lowerStarId A V) ≪≫
    Functor.rightDerivedFunctorPlusIdIso _

/-- The characterization of `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus`: composing the
unit of the right derived functor with it gives the levelwise image of
`AlgebraicGeometry.Etale.lowerStarId`. -/
lemma lowerStarIdDerivedPlus_hom_app_fac
    (K : HomotopyCategory.Plus (Sheaf V.smallEtaleTopology A)) :
    ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnit.app K ≫
        (lowerStarIdDerivedPlus A V).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).hom).app K) := by
  have hn : (Functor.rightDerivedFunctorPlusNatIso (Etale.lowerStarId A V)).hom =
      Functor.rightDerivedFunctorPlusNatTrans (Etale.lowerStarId A V).hom := rfl
  rw [lowerStarIdDerivedPlus, Iso.trans_hom, NatTrans.comp_app, hn, ← Category.assoc,
    Functor.rightDerivedFunctorPlusNatTrans_app, Category.assoc,
    Functor.rightDerivedFunctorPlusIdIso_fac_app,
    Functor.mapHomotopyCategoryPlusIdIso_hom_app_eq_id]
  have hid : DerivedCategory.Plus.Qh.map (𝟙 K) = 𝟙 (DerivedCategory.Plus.Qh.obj K) :=
    DerivedCategory.Plus.Qh.map_id K
  rw [hid]
  exact Category.comp_id _

/-- The inverse form of `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus_hom_app_fac`: on the
image of a bounded below complex, the inverse of
`AlgebraicGeometry.Etale.lowerStarIdDerivedPlus` is the levelwise image of the inverse of
`AlgebraicGeometry.Etale.lowerStarId` followed by the unit of the right derived functor. -/
lemma lowerStarIdDerivedPlus_inv_app
    (K : HomotopyCategory.Plus (Sheaf V.smallEtaleTopology A)) :
    (lowerStarIdDerivedPlus A V).inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K) ≫
        ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnit.app K := by
  rw [← cancel_mono ((lowerStarIdDerivedPlus A V).hom.app (DerivedCategory.Plus.Qh.obj K)),
    Iso.inv_hom_id_app, Category.assoc, lowerStarIdDerivedPlus_hom_app_fac,
    ← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
    NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app]
  exact (DerivedCategory.Plus.Qh.map_id _).symm

/-- **The derived unit for the identity morphism**: the unit of the bounded below derived
adjunction `D(𝟙 V)^*⁺ ⊣ R(𝟙 V)_*⁺` is, modulo the identity isomorphism
`AlgebraicGeometry.Etale.upperStarIdDerivedPlus` of the pullback, the inverse of the
identity isomorphism `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus` of the pushforward. -/
lemma derivedPlus_unit_comp_upperStarIdDerivedPlus :
    (Etale.upperStarLowerStarAdjunction A (𝟙 V)).derivedPlus.unit ≫
        Functor.whiskerRight (upperStarIdDerivedPlus A V).hom
          (((𝟙 V)_*[A]).rightDerivedFunctorPlus) =
      (lowerStarIdDerivedPlus A V).inv := by
  rw [← cancel_epi (lowerStarIdDerivedPlus A V).hom, Iso.hom_inv_id]
  refine Functor.rightDerived_ext (((𝟙 V)_*[A]).rightDerivedFunctorPlus)
    (((𝟙 V)_*[A]).rightDerivedFunctorPlusUnit) (HomotopyCategory.Plus.quasiIso _) _ _ _ ?_
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app]
  have hnat : DerivedCategory.Plus.Qh.map (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K)) ≫
      ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnit.app
        ((𝟭 (Sheaf V.smallEtaleTopology A)).mapHomotopyCategoryPlus.obj K) =
      ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnit.app
          (((𝟙 V)^*[A]).mapHomotopyCategoryPlus.obj K) ≫
        ((𝟙 V)_*[A]).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K)) :=
    ((𝟙 V)_*[A]).rightDerivedFunctorPlusUnit.naturality _
  have hcomb : (NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).hom).app K ≫
      (Etale.upperStarLowerStarAdjunction A (𝟙 V)).mapHomotopyCategoryPlus.unit.app K ≫
        ((𝟙 V)_*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K) =
      𝟙 (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.obj K) := by
    rw [Adjunction.mapHomotopyCategoryPlus_unit_app_comp
        (Etale.upperStarLowerStarAdjunction A (𝟙 V)) (Etale.upperStarId A V)
        (Etale.lowerStarId A V) (Etale.upperStarId_hom_app_unit_app A V) K,
      ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.hom_inv_id]
    exact NatTrans.congr_app (NatTrans.mapHomotopyCategoryPlus_id ((𝟙 V)_*[A])) K
  have hQ : DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).hom).app K) ≫
      DerivedCategory.Plus.Qh.map
        ((Etale.upperStarLowerStarAdjunction A (𝟙 V)).mapHomotopyCategoryPlus.unit.app K) ≫
        DerivedCategory.Plus.Qh.map (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A V).hom).app K)) =
      𝟙 (DerivedCategory.Plus.Qh.obj (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.obj K)) := by
    rw [← DerivedCategory.Plus.Qh.map_comp, ← DerivedCategory.Plus.Qh.map_comp]
    exact (congrArg DerivedCategory.Plus.Qh.map hcomb).trans
      (DerivedCategory.Plus.Qh.map_id _)
  rw [← Category.assoc, lowerStarIdDerivedPlus_hom_app_fac, upperStarIdDerivedPlus_hom_app,
    Functor.map_comp, Adjunction.derivedPlus_unit_app_fac_assoc, ← hnat, reassoc_of% hQ]
  exact (Category.comp_id (((𝟙 V)_*[A]).rightDerivedFunctorPlusUnit.app K)).symm

variable {V}

/-- The composition isomorphism `Functor.rightDerivedFunctorPlusCompIso'` cancels the
identity isomorphism `AlgebraicGeometry.Etale.lowerStarIdDerivedPlus`, provided the
underlying isomorphism `e` of pushforwards cancels
`AlgebraicGeometry.Etale.lowerStarId`. -/
lemma lowerStarIdDerivedPlus_inv_comp_rightDerivedFunctorPlusCompIso' (g : V ⟶ Y)
    [(((𝟙 V)_*[A])).PreservesInjectiveObjects]
    (e : ((𝟙 V)_*[A]) ⋙ ((g)_*[A]) ≅ (g)_*[A])
    (he : Functor.whiskerRight (Etale.lowerStarId A V).inv ((g)_*[A]) ≫ e.hom =
      𝟙 ((g)_*[A])) :
    Functor.whiskerRight (lowerStarIdDerivedPlus A V).inv
          (((g)_*[A]).rightDerivedFunctorPlus) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((𝟙 V)_*[A]) ((g)_*[A]) e).hom =
      𝟙 (((g)_*[A]).rightDerivedFunctorPlus) := by
  refine Functor.rightDerived_ext (((g)_*[A]).rightDerivedFunctorPlus)
    (((g)_*[A]).rightDerivedFunctorPlusUnit) (HomotopyCategory.Plus.quasiIso _) _ _ _ ?_
  ext K : 2
  have hnat : DerivedCategory.Plus.Qh.map (((g)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K)) ≫
      ((g)_*[A]).rightDerivedFunctorPlusUnit.app
        (((𝟙 V)_*[A]).mapHomotopyCategoryPlus.obj K) =
      ((g)_*[A]).rightDerivedFunctorPlusUnit.app K ≫
        ((g)_*[A]).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K)) :=
    ((g)_*[A]).rightDerivedFunctorPlusUnit.naturality _
  have hfac := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac
    ((𝟙 V)_*[A]) ((g)_*[A]) e) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hfac ⊢
  have hfac2 := (Functor.rightDerivedFunctorPlusCompUnit_app_assoc ((𝟙 V)_*[A]) ((g)_*[A]) K
    ((Functor.rightDerivedFunctorPlusCompIso' ((𝟙 V)_*[A]) ((g)_*[A]) e).hom.app
      (DerivedCategory.Plus.Qh.obj K))).symm.trans hfac
  have hm : ((g)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K) =
      (NatTrans.mapHomotopyCategoryPlus
        (Functor.whiskerRight (Etale.lowerStarId A V).inv ((g)_*[A]))).app K := rfl
  have hcomp : ((g)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K) ≫
      (NatTrans.mapHomotopyCategoryPlus e.hom).app K =
      𝟙 (((g)_*[A]).mapHomotopyCategoryPlus.obj K) := by
    rw [hm, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, he]
    exact NatTrans.congr_app (NatTrans.mapHomotopyCategoryPlus_id ((g)_*[A])) K
  have hQ : DerivedCategory.Plus.Qh.map (((g)_*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus (Etale.lowerStarId A V).inv).app K)) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) =
      𝟙 (DerivedCategory.Plus.Qh.obj (((g)_*[A]).mapHomotopyCategoryPlus.obj K)) :=
    (DerivedCategory.Plus.Qh.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Plus.Qh.map hcomp).trans
        (DerivedCategory.Plus.Qh.map_id _))
  rw [lowerStarIdDerivedPlus_inv_app, Functor.map_comp, Category.assoc,
    ← reassoc_of% hnat, hfac2, reassoc_of% hQ]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

variable (c)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The composition isomorphism of pushforwards attached to the identity refinement cancels
the identity isomorphism `AlgebraicGeometry.Etale.lowerStarId`. -/
lemma refinementLowerStarComp_id :
    Functor.whiskerRight (Etale.lowerStarId A c.Z).inv ((c.g)_*[A]) ≫
        (refinementLowerStarComp A (Compactification.Refinement.id c)).hom =
      𝟙 ((c.g)_*[A]) := by
  have hgen : ∀ {W W' : Scheme.{u}} (h₁ : c.Z ⟶ W) (h₂ : W ⟶ W') (h₁₂ : c.Z ⟶ W')
      (hh₁₂ : h₁₂ = h₁ ≫ h₂),
      Etale.lowerStarComp A h₁ h₂ h₁₂ hh₁₂ ≪≫
          eqToIso (congrArg (fun g => (g)_*[A]) hh₁₂) = Etale.lowerStarComp A h₁ h₂ := by
    intro W W' h₁ h₂ h₁₂ hh₁₂
    subst hh₁₂
    simp
  have hr : refinementLowerStarComp A (Compactification.Refinement.id c) =
      Etale.lowerStarComp A (𝟙 c.Z) c.g ≪≫
        eqToIso (congrArg (fun g => (g)_*[A]) (Category.id_comp c.g)) := rfl
  rw [hr, ← hgen (𝟙 c.Z) c.g c.g (Category.id_comp c.g).symm, Etale.lowerStarComp_id_left]
  ext G
  simp

/-- **The identity refinement has trivial base change**: the inverse of the base change
isomorphism attached to `Compactification.Refinement.id c` is the whiskering of the identity
isomorphism `AlgebraicGeometry.Etale.upperStarIdDerivedPlus`. -/
lemma refinementLowerShriekBaseChangeDerivedPlusIso_inv_id
    (hcart : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i) :
    (refinementLowerShriekBaseChangeDerivedPlusIso A
        (Compactification.Refinement.id c) hcart).inv =
      Functor.whiskerLeft ((c.i)_!open[A].mapDerivedCategoryPlus)
        (upperStarIdDerivedPlus A c.Z).hom := by
  rw [← cancel_epi (refinementLowerShriekBaseChangeDerivedPlusIso A
    (Compactification.Refinement.id c) hcart).hom, Iso.hom_inv_id]
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso _) (fun K => ?_)
  have hbc : (refinementLowerShriekBaseChangeDerivedPlusIso A
        (Compactification.Refinement.id c) hcart).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
      ((𝟙 c.Z)^*[A]).mapDerivedCategoryPlus.map
        (((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      ((𝟙 c.Z)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K) =
      ((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          ((Compactification.Refinement.id c).openImmersionLowerShriekBaseChange A)).app K) :=
    refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh A
      (Compactification.Refinement.id c) hcart K
  simp only [NatTrans.id_app, NatTrans.comp_app, Functor.whiskerLeft_app]
  symm
  rw [← cancel_mono (((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K),
    Category.assoc, Category.id_comp]
  have hnat := ((upperStarIdDerivedPlus A c.Z).hom.naturality
    (((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K))
  simp only [Functor.id_map, Functor.comp_obj] at hnat
  rw [← hnat, upperStarIdDerivedPlus_hom_app, reassoc_of% hbc]
  have hbcid : (Compactification.Refinement.id c).openImmersionLowerShriekBaseChange A =
      Functor.whiskerLeft (c.i)_!open[A] (Etale.upperStarId A c.Z).inv := by
    rw [Compactification.Refinement.openImmersionLowerShriekBaseChange_id]
    ext S
    simp
  have hbridge : (NatTrans.mapHomotopyCategoryPlus
        (Functor.whiskerLeft (c.i)_!open[A] (Etale.upperStarId A c.Z).inv)).app K =
      (NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A c.Z).inv).app
        (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K) := rfl
  have hcancel : (NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A c.Z).inv).app
        (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K) ≫
      (NatTrans.mapHomotopyCategoryPlus (Etale.upperStarId A c.Z).hom).app
        (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategoryPlus_comp, Iso.inv_hom_id,
      NatTrans.mapHomotopyCategoryPlus_id, NatTrans.id_app]
  have hid : DerivedCategory.Plus.Qh.map (𝟙 ((𝟭 (Sheaf c.Z.smallEtaleTopology A)
        ).mapHomotopyCategoryPlus.obj (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K))) =
      𝟙 (DerivedCategory.Plus.Qh.obj ((𝟭 (Sheaf c.Z.smallEtaleTopology A)
        ).mapHomotopyCategoryPlus.obj (((c.i)_!open[A]).mapHomotopyCategoryPlus.obj K))) :=
    DerivedCategory.Plus.Qh.map_id _
  rw [hbcid, hbridge, ← DerivedCategory.Plus.Qh.map_comp, hcancel, hid]
  exact Category.comp_id _

/-- **The identity law for the comparison of derived lower shrieks**: the comparison
`Rf_!(c)[A]+ ⟶ Rf_!(c)[A]+` attached to the identity refinement of a compactification `c`
is the identity. (blueprint: `BA43-RHO`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusComparison_id
    (hcart : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i) :
    rightDerivedLowerShriekOfCompactificationPlusComparison A
      (Compactification.Refinement.id c) hcart = 𝟙 (Rf_!(c)[A]+) := by
  have : (((𝟙 c.Z)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A (𝟙 c.Z))
  have : (((Compactification.Refinement.id c).hom)_*[A]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A (Compactification.Refinement.id c).hom)
  ext W : 2
  have hB := NatTrans.congr_app (derivedPlus_unit_comp_upperStarIdDerivedPlus A c.Z)
    (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  have hC := NatTrans.congr_app
    (lowerStarIdDerivedPlus_inv_comp_rightDerivedFunctorPlusCompIso' A c.g
      (refinementLowerStarComp A (Compactification.Refinement.id c))
      (refinementLowerStarComp_id A c))
    (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  have hBC := NatTrans.congr_app
    (refinementLowerShriekBaseChangeDerivedPlusIso_inv_id A c hcart) W
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hB hC ⊢
  have hB' : (Etale.upperStarLowerStarAdjunction A
        (Compactification.Refinement.id c).hom).derivedPlus.unit.app
        (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
      (((Compactification.Refinement.id c).hom)_*[A]).rightDerivedFunctorPlus.map
        ((upperStarIdDerivedPlus A c.Z).hom.app
          (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)) =
      (lowerStarIdDerivedPlus A c.Z).inv.app
        (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W) := hB
  have hC' : ((c.g)_*[A]).rightDerivedFunctorPlus.map
        ((lowerStarIdDerivedPlus A c.Z).inv.app
          (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)) ≫
      (Functor.rightDerivedFunctorPlusCompIso' (((Compactification.Refinement.id c).hom)_*[A])
          ((c.g)_*[A])
          (refinementLowerStarComp A (Compactification.Refinement.id c))).hom.app
        (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W) =
      𝟙 (((c.g)_*[A]).rightDerivedFunctorPlus.obj
        (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)) := hC
  simp only [rightDerivedLowerShriekOfCompactificationPlusComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map]
  rw [hBC, Functor.whiskerLeft_app, ← Functor.map_comp_assoc, hB', hC']
  rfl

end IdentityLaw

end Etale

end AlgebraicGeometry
