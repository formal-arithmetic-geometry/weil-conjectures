/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X6
-/
module

public import Sheaf.Paper.LisseTowerPulledScalar

/-! # Functor comparisons for localization of finite coefficient modules

Source: Stacks Project, Modules on Sites, Tags 03CY, 03D2 and 03D3, and
Cohomology on Sites, Tag 0D6D. These comparisons concern inverse image and scalar restriction;
they do not involve a descended tower or choices of its level markings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  lisseTowerFixedRealization constantAdicFiniteProjection localProEtaleNormalization
  adicTowerRestrictedTransition lisseTowerPulledScalarIso lisseTowerEtaleScalarIso
  constantAdicRestrictedStep

/-- Inverse image of an arbitrary semilinear finite-coefficient arrow, using the
specified coefficient mate. This is the operation used by adicTowerRestrictedTransition.
Source: Stacks Tags 03D2 and 03D3.
(blueprint: lem-weil-pbc-lisse-tower-localization-comparisons). -/
def lisseTowerInverseImageArrow {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    {C : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op (n + 1))))}
    {C' : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))}
    (t : C ⟶ (pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj C') :
    (adicTowerPullback g ((pbcAdicRings X d).obj (op (n + 1)))).obj C ⟶
      (pbcDerivedRestrict ((adicTowerInverseImage g).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).obj
        ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj C') :=
  (adicTowerPullback g ((pbcAdicRings X d).obj (op (n + 1)))).map t ≫
    (proEtaleRingRestrictionDerivedPullback g
      ((pbcAdicRings X d).obj (op (n + 1))) ((pbcAdicRings X d).obj (op n))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op (n + 1))))
      ((adicTowerInverseImage g).obj ((pbcAdicRings X d).obj (op n)))
      (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)).inv.app C'

/-- Further restriction of an inverse-image arrow to completion coefficients.
Source: Stacks Tags 03DA and 0D6D.
(blueprint: lem-weil-pbc-lisse-tower-localization-comparisons). -/
def lisseTowerProjectedArrow {X Z : Scheme.{u}} (g : Z ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    {C : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op (n + 1))))}
    {C' : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n)))}
    (t : C ⟶ (pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj C') :=
  (pbcDerivedRestrict (constantAdicFiniteProjection g d (n + 1))).map
      (lisseTowerInverseImageArrow g d n t) ≫
    (pbcDerivedRestrictComp (constantAdicFiniteProjection g d (n + 1))
      ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
      (constantAdicFiniteProjection g d n)
      (constantAdicFiniteProjection_comp g d (n + 1) n (Nat.le_succ n))).hom.app
        ((adicTowerPullback g ((pbcAdicRings X d).obj (op n))).obj C')

attribute [local irreducible] pbcDerivedRestrict
  lisseTowerInverseImageArrow lisseTowerProjectedArrow

/-- Comparisons of the localization functors, including their two scalar faces.
The level comparisons are natural transformations of functors, rather than arbitrary
isomorphisms between their values. The source face contains no level marking, and
the target face contains no etale model or descent equation.
Source: Stacks Tags 03CY, 03D2, 03D3 and 0D6D.
(blueprint: lem-weil-pbc-lisse-tower-localization-comparisons). -/
structure LisseTowerLocalizationComparisons
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) where
  pull : ∀ n : ℕ,
    DerivedCategory (pbcModules U.left
      ((adicTowerInverseImage (U.hom ≫ g)).obj ((pbcAdicRings X d).obj (op n)))) ⥤
    DerivedCategory (pbcModules W.left
      ((adicTowerInverseImage (W.hom ≫ g)).obj ((pbcAdicRings X d).obj (op n))))
  level : ∀ n : ℕ,
    localProEtaleComparison V.hom (lisseTowerEtaleRing d n) ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))
          f.left).mapDerivedCategory ⋙ lisseTowerFixedRealization (W.hom ≫ g) d n ≅
      lisseTowerEtaleRealization (U.hom ≫ g) d n ⋙ pull n
  base : ∀ n : ℕ,
    adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n)) ⋙ pull n ≅
      adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))
  scalar : ∀ n : ℕ,
    pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) ⋙ pull (n + 1) ⋙
        pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d (n + 1)) ≅
      pull n ⋙ pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d n)
  source : ∀ (n : ℕ) (c : LisseTowerScalarSquare (U.hom ≫ g) d n),
    LisseTowerScalarSquareSections (U.hom ≫ g) d n c →
    ∀ (C : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))))
      (C' : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
      (δ : C ⟶
        (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj
          C'),
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d j
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
    (H (n + 1)).map ((L (n + 1)).map
        (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) δ)) ≫
        (lisseTowerPulledScalarIso (W.hom ≫ g) f.left d n).hom.app
          ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj C') ≫
        (H n).map ((level n).hom.app C') =
      (H (n + 1)).map ((level (n + 1)).hom.app C) ≫
        (pull (n + 1) ⋙ H (n + 1)).map
          ((lisseTowerEtaleRealization (U.hom ≫ g) d (n + 1)).map δ ≫
            (lisseTowerEtaleScalarIso (U.hom ≫ g) d n c).hom.app C') ≫
        (scalar n).hom.app ((lisseTowerEtaleRealization (U.hom ≫ g) d n).obj C')
  target : ∀ (n : ℕ)
    (C : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op (n + 1)))))
    (C' : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (t : C ⟶ (pbcDerivedRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))).obj C'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
    (pull (n + 1) ⋙ H (n + 1)).map
        (lisseTowerInverseImageArrow (U.hom ≫ g) d n t) ≫
        (scalar n).hom.app
          ((adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj C') ≫
        (H n).map ((base n).hom.app C') =
      (H (n + 1)).map ((base (n + 1)).hom.app C) ≫
        lisseTowerProjectedArrow (W.hom ≫ g) d n t

/-- Inverse image admits simultaneous functor comparisons compatible with finite
scalar restriction. This asserts the two faces of the coefficient cube before
applying any descended transition equation or level marking.

Source: Stacks Project, Modules on Sites, Tags 03CY, 03D2 and 03D3 (sheafification
and inverse image of modules), and Cohomology on Sites, Tag 0D6D (composition).
(blueprint: lem-weil-pbc-lisse-tower-localization-comparisons).

Proof: put a = f.left followed by V.hom. The equation f.w and associativity identify
its composite with U.hom followed by g with W.hom followed by g. At level n take
exact module inverse image along a, transporting the resulting coefficient ring by
the canonical inverse-image compositor and this equality. This is pull n. The
canonical sheafification/inverse-image comparison, with the etale/pro-etale comparison
compositor, gives level n. The module inverse-image compositor gives base n.
Restrict along the actual inverse images of the finite quotient maps. The exact
coefficient mate, followed by the restriction compositor for the finite projections,
gives scalar n. All these comparisons are induced on the underlying abelian sheaves
by the canonical inverse-image compositors. The section normalization of c and of
lisseTowerNormalizedScalarSquare identifies their two scalar faces. Forgetting module
actions is faithful, so the source cube commutes on sheaves. Exact localization,
naturality at delta, and mapDerivedCategoryCompIso give source. For target use the
same inverse-image composition cube on an arbitrary semilinear arrow t: naturality
of base moves its arrow, and the coefficient mate identifies its restricted images.
After the finite projection restriction compositor this is constantAdicRestrictedStep
for an adic transition, and lisseTowerProjectedArrow in general, proving target.
No choice of a marking is involved. Zero modules and
empty sites satisfy the same identities of natural transformations.
-/
theorem lisseTower_localization_comparisons
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) :
    Nonempty (LisseTowerLocalizationComparisons X Y g d U V W f) := by
  sorry

end AlgebraicGeometry.Scheme
