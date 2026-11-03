/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-! # The canonical compact-support scalar/site square

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-exceptional.proof.md, Charts; Stacks Tags 09A6, 09AF,
07A7, 0D6D and 0GL1 (blueprint: lem-sp-finite-ctf-site-coefficient-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- The canonical compact-support site comparison: the proper counit mate followed
by the exact open-extension comparison. This is a map of ordinary constant-ring
module derived categories, with no realization data.
Source: Stacks 09A6 and 09AF (blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfCompactSiteMap (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : Etale.DerivedCategoryModule R X) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.obj
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj L) ⟶
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c).obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj L) :=
  (ProEtale.directImageComparisonAmbient R c.g).app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj L) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctor.map
      ((ProEtale.mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} R) c.i).hom.app L)

/-- The pro-etale proper B-linear transpose of the scalar-extended A-counit,
followed by the canonical open balancing map.
Source: Stacks 07A7 and 0GL1 (blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def finiteCtfProEtaleScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (ProEtale.pbcFixedScalarExtension (ProEt.topology Y) φ).obj
        ((ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ⟶
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((ProEtale.pbcFixedScalarExtension (ProEt.topology X) φ).obj M) :=
  (mateEquiv
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) c.g)
    (TwoSquare.mk _ _ _ _ (ProEtale.scalarPullbackProEtaleIso φ c.g).hom)).natTrans.app
      ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
      ((ProEtale.OpenScalarSite.scalarOpen φ c.i).hom.app M)

/-- The displayed square of actual constant-ring derived maps. The named maps
are the canonical proper/open composites; delta is the canonical tensor/site map.
Source: latest blueprint, Charts; Stacks 07A7, 09AF and 0D6D
(blueprint: lem-sp-finite-ctf-site-coefficient-square). -/
def FiniteCtfSiteCoefficientSquare
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : Etale.DerivedCategoryModule A X) : Prop :=
  (ProEtale.pbcFixedScalarExtension (ProEt.topology Y) φ).map
      (finiteCtfCompactSiteMap A c L) ≫
    finiteCtfProEtaleScalarMap φ c
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L) ≫
    (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
      ((ProEtale.pbcComparisonReduction X φ).hom.app L) =
  (ProEtale.pbcComparisonReduction Y φ).hom.app
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L) ≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map
      ((Etale.compactScalarMap φ c).app L) ≫
    finiteCtfCompactSiteMap B c ((Etale.scalarExtension φ X).obj L)

end AlgebraicGeometry
