/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Compactification.RefinementPullback
public import WeilConjectures.SixFunctors.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Derived.UpperLowerStar
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

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison_comp`:
  the composition law, i.e. the comparison attached to a composite `r.comp s` of
  refinements is the composite of the two comparisons. Since the comparison runs from the
  coarser to the finer compactification, it is contravariant in the refinement and the
  order of the composite is reversed.

## Implementation notes

Only the bounded below variant is constructed. The unbounded variant would need both the
unbounded derived adjunction `Dq^* ⊣ Rq_*` and the unbounded composition isomorphism for
derived pushforwards, neither of which is available.

That the comparison is an isomorphism is proper base change and is not proved here.

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

The composition law repeats that architecture one level up, and is assembled from three
cocycle laws: the base change isomorphisms compose
(`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso_inv_comp`), the
derived units compose modulo the composition isomorphism
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` of the derived pullbacks
(`AlgebraicGeometry.Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus`), and the
composition isomorphisms of the derived pushforwards are associative
(`Functor.rightDerivedFunctorPlusCompIso'_assoc`, applied through the underived
associativity `AlgebraicGeometry.Etale.refinementLowerStarComp_comp`).

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

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

variable (c)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
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

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

section CompositionLaw

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The composition isomorphism of pushforwards attached to a refinement is the composition
isomorphism `AlgebraicGeometry.Etale.lowerStarComp` at the structure morphism of the
finer compactification. -/
lemma refinementLowerStarComp_eq {c d : Compactification f} (r : c.Refinement d) :
    refinementLowerStarComp A r = Etale.lowerStarComp A r.hom d.g c.g r.hom_g.symm := by
  have h : refinementLowerStarComp A r =
      Etale.lowerStarComp A r.hom d.g ≪≫
        eqToIso (congrArg (fun g => (g)_*[A]) r.hom_g) := rfl
  rw [h, Etale.lowerStarComp_trans_eqToIso A r.hom d.g c.g r.hom_g]

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- **Cocycle law for the composition isomorphism of pushforwards along a refinement**. -/
lemma refinementLowerStarComp_comp {c d e : Compactification f}
    (r : c.Refinement d) (s : d.Refinement e) :
    Functor.whiskerRight
          (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl).hom ((e.g)_*[A]) ≫
        (refinementLowerStarComp A (r.comp s)).hom =
      Functor.whiskerLeft ((r.hom)_*[A]) (refinementLowerStarComp A s).hom ≫
        (refinementLowerStarComp A r).hom := by
  rw [Etale.refinementLowerStarComp_eq, Etale.refinementLowerStarComp_eq,
    Etale.refinementLowerStarComp_eq]
  exact Etale.lowerStarComp_assoc' A r.hom s.hom e.g ((r.comp s).hom) d.g c.g rfl
    s.hom_g.symm ((r.comp s).hom_g).symm

/-- **Cocycle law for the base change isomorphism on the bounded below derived
categories**. -/
lemma refinementLowerShriekBaseChangeDerivedPlusIso_hom_comp
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A (r.comp s)
          (Compactification.Refinement.isPullback_comp r s hr hs)).hom ≫
        Functor.whiskerLeft ((e.i)_!open[A]).mapDerivedCategoryPlus
          (Etale.upperStarCompDerivedPlus A r.hom s.hom ((r.comp s).hom) rfl).hom =
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).hom ≫
        Functor.whiskerRight
          (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).hom
          (((r.hom)^*[A]).mapDerivedCategoryPlus) := by
  have hcocycle : (r.comp s).openImmersionLowerShriekBaseChange A ≫
      Functor.whiskerLeft ((e.i)_!open[A])
        (Etale.upperStarComp A r.hom s.hom ((r.comp s).hom) rfl).hom =
      r.openImmersionLowerShriekBaseChange A ≫
        Functor.whiskerRight (s.openImmersionLowerShriekBaseChange A)
          ((r.hom)^*[A]) := by
    have h : (r.comp s).openImmersionLowerShriekBaseChange A =
        r.openImmersionLowerShriekBaseChange A ≫
          Functor.whiskerRight (s.openImmersionLowerShriekBaseChange A) ((r.hom)^*[A]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft ((e.i)_!open[A])
            (Etale.upperStarComp A r.hom s.hom ((r.comp s).hom) rfl).inv :=
      Compactification.Refinement.openImmersionLowerShriekBaseChange_comp A r s
    rw [h]
    ext W
    simp
  refine Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso _) (fun K => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← cancel_mono (((r.hom)^*[A]).mapDerivedCategoryPlus.map
      (((s.hom)^*[A]).mapDerivedCategoryPlus.map
        (((e.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K)) ≫
    ((r.hom)^*[A]).mapDerivedCategoryPlus.map
      (((s.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K)) ≫
    ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
      (((s.hom)^*[A]).mapHomotopyCategoryPlus.obj
        (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K)))]
  simp only [Category.assoc]
  have hnatPhi := (Etale.upperStarCompDerivedPlus A r.hom s.hom ((r.comp s).hom)
      rfl).hom.naturality (((e.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatPhi
  have hBs := congrArg (((r.hom)^*[A]).mapDerivedCategoryPlus.map)
    (Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh A s hs K)
  simp only [Functor.map_comp] at hBs
  have hnatF1 : ((r.hom)^*[A]).mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus
          (s.openImmersionLowerShriekBaseChange A)).app K)) ≫
      ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
        (((s.hom)^*[A]).mapHomotopyCategoryPlus.obj
          (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K)) =
      ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          (((d.i)_!open[A]).mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map (((r.hom)^*[A]).mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus
            (s.openImmersionLowerShriekBaseChange A)).app K)) :=
    ((r.hom)^*[A]).mapDerivedCategoryPlusFactorsh.hom.naturality _
  have hbrL : (NatTrans.mapHomotopyCategoryPlus
        (Etale.upperStarComp A r.hom s.hom ((r.comp s).hom) rfl).hom).app
        (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K) =
      (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerLeft ((e.i)_!open[A])
        (Etale.upperStarComp A r.hom s.hom ((r.comp s).hom) rfl).hom)).app K := rfl
  have hbrR : ((r.hom)^*[A]).mapHomotopyCategoryPlus.map
        ((NatTrans.mapHomotopyCategoryPlus
          (s.openImmersionLowerShriekBaseChange A)).app K) =
      (NatTrans.mapHomotopyCategoryPlus (Functor.whiskerRight
        (s.openImmersionLowerShriekBaseChange A) ((r.hom)^*[A]))).app K := rfl
  trans ((c.i)_!open[A]).mapDerivedCategoryPlusFactorsh.hom.app K ≫
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
      (r.openImmersionLowerShriekBaseChange A ≫ Functor.whiskerRight
        (s.openImmersionLowerShriekBaseChange A) ((r.hom)^*[A]))).app K)
  · rw [← reassoc_of% hnatPhi, Etale.upperStarCompDerivedPlus_hom_app_factorsh A r.hom
        s.hom ((r.comp s).hom) rfl (((e.i)_!open[A]).mapHomotopyCategoryPlus.obj K),
      Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh_assoc,
      hbrL, ← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategoryPlus_comp, hcocycle]
  · rw [reassoc_of% hBs, hnatF1,
      Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_app_factorsh_assoc,
      hbrR, ← DerivedCategory.Plus.Qh.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomotopyCategoryPlus_comp]

/-- The inverse form of
`AlgebraicGeometry.Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_comp`. -/
lemma refinementLowerShriekBaseChangeDerivedPlusIso_inv_comp
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A (r.comp s)
          (Compactification.Refinement.isPullback_comp r s hr hs)).inv =
      Functor.whiskerLeft ((e.i)_!open[A]).mapDerivedCategoryPlus
          (Etale.upperStarCompDerivedPlus A r.hom s.hom ((r.comp s).hom) rfl).hom ≫
        Functor.whiskerRight
            (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv
            (((r.hom)^*[A]).mapDerivedCategoryPlus) ≫
          (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv := by
  rw [← cancel_epi (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A (r.comp s)
      (Compactification.Refinement.isPullback_comp r s hr hs)).hom, Iso.hom_inv_id,
    ← Category.assoc,
    Etale.refinementLowerShriekBaseChangeDerivedPlusIso_hom_comp A r s hr hs]
  have h1 : Functor.whiskerRight
        (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).hom
        (((r.hom)^*[A]).mapDerivedCategoryPlus) ≫
      Functor.whiskerRight
        (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv
        (((r.hom)^*[A]).mapDerivedCategoryPlus) = 𝟙 _ :=
    (Functor.isoWhiskerRight
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs)
      (((r.hom)^*[A]).mapDerivedCategoryPlus)).hom_inv_id
  rw [Category.assoc, reassoc_of% h1, Iso.hom_inv_id]

/-- **The composition law for the comparison of derived lower shrieks**: the comparison
attached to a composite `r.comp s` of refinements is the composite of the two comparisons.
Note that, the comparison running from the coarser to the finer compactification, the order
of the composite is reversed. (blueprint: `BA43-RHO`) -/
theorem rightDerivedLowerShriekOfCompactificationPlusComparison_comp
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) (hs : IsPullback d.i (𝟙 X) s.hom e.i) :
    Etale.rightDerivedLowerShriekOfCompactificationPlusComparison A (r.comp s)
        (Compactification.Refinement.isPullback_comp r s hr hs) =
      Etale.rightDerivedLowerShriekOfCompactificationPlusComparison A s hs ≫
        Etale.rightDerivedLowerShriekOfCompactificationPlusComparison A r hr := by
  have hI1 : (((r.hom)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A r.hom)
  have hI2 : (((s.hom)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A s.hom)
  have hI : ((((r.comp s).hom)_*[A])).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A (r.comp s).hom)
  ext W : 2
  have hBCinv := NatTrans.congr_app
    (Etale.refinementLowerShriekBaseChangeDerivedPlusIso_inv_comp A r s hr hs) W
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hBCinv
  have hstep2 := Etale.derivedPlus_unit_comp_upperStarCompDerivedPlus A r.hom s.hom
    ((r.comp s).hom) rfl (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  have hstep3 := NatTrans.congr_app
    (Functor.rightDerivedFunctorPlusCompIso'_assoc ((r.hom)_*[A]) ((s.hom)_*[A])
      ((e.g)_*[A]) (((r.comp s).hom)_*[A]) ((d.g)_*[A]) ((c.g)_*[A])
      (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl)
      (refinementLowerStarComp A s) (refinementLowerStarComp A (r.comp s))
      (refinementLowerStarComp A r) (Etale.refinementLowerStarComp_comp A r s))
    (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hstep3
  have hnatXi := (Functor.rightDerivedFunctorPlusCompIso' ((r.hom)_*[A]) ((s.hom)_*[A])
      (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl)).hom.naturality
    (((r.hom)^*[A]).mapDerivedCategoryPlus.map
        ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W) ≫
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W)
  simp only [Functor.comp_obj, Functor.comp_map] at hnatXi
  have hnatEta1 := (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.naturality
    ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hnatEta1
  have hnatTs := (Functor.rightDerivedFunctorPlusCompIso' ((s.hom)_*[A]) ((e.g)_*[A])
      (refinementLowerStarComp A s)).hom.naturality
    ((Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
        (((d.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
      ((r.hom)_*[A]).rightDerivedFunctorPlus.map
        ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W))
  simp only [Functor.comp_obj, Functor.comp_map] at hnatTs
  have hinner : (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
        (((s.hom)^*[A]).mapDerivedCategoryPlus.obj
          (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W)) ≫
      ((r.hom)_*[A]).rightDerivedFunctorPlus.map
        (((r.hom)^*[A]).mapDerivedCategoryPlus.map
            ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W) ≫
          (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W) =
      (Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W ≫
        (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
          (((d.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
        ((r.hom)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W) := by
    rw [Functor.map_comp, ← reassoc_of% hnatEta1]
  have hcore : (Etale.upperStarLowerStarAdjunction A (r.comp s).hom).derivedPlus.unit.app
        (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
      ((((r.comp s).hom)_*[A])).rightDerivedFunctorPlus.map
        ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A (r.comp s)
          (Compactification.Refinement.isPullback_comp r s hr hs)).inv.app W) =
      (Etale.upperStarLowerStarAdjunction A s.hom).derivedPlus.unit.app
          (((e.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
        ((s.hom)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A s hs).inv.app W) ≫
        ((s.hom)_*[A]).rightDerivedFunctorPlus.map
          ((Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit.app
              (((d.i)_!open[A]).mapDerivedCategoryPlus.obj W) ≫
            ((r.hom)_*[A]).rightDerivedFunctorPlus.map
              ((Etale.refinementLowerShriekBaseChangeDerivedPlusIso A r hr).inv.app W)) ≫
        (Functor.rightDerivedFunctorPlusCompIso' ((r.hom)_*[A]) ((s.hom)_*[A])
            (Etale.lowerStarComp A r.hom s.hom ((r.comp s).hom) rfl)).hom.app
          (((c.i)_!open[A]).mapDerivedCategoryPlus.obj W) := by
    rw [hBCinv, Functor.map_comp, ← Category.assoc, hstep2, Category.assoc, Category.assoc,
      ← hnatXi, ← Functor.map_comp_assoc, hinner, Functor.map_comp, Category.assoc]
  simp only [Etale.rightDerivedLowerShriekOfCompactificationPlusComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map]
  rw [← Functor.map_comp_assoc, hcore, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hstep3]
  conv_rhs =>
    rw [← Functor.map_comp_assoc (((d.g)_*[A]).rightDerivedFunctorPlus),
      ← reassoc_of% hnatTs]

end CompositionLaw

end Etale

end AlgebraicGeometry
