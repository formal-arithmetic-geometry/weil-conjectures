/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarPullNormalization
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarPullbackCube
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube

/-! # Scalar and geometric site squares, with their right-adjoint mates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem sitePull_eq (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) :
    Sites.sitePull A g = ProEtale.directImageComparisonAmbientPullbackIso A g := by
  apply Iso.ext
  ext M
  simp only [Sites.sitePull, ProEtale.directImageComparisonAmbientPullbackIso,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, Sites.nu]

/-- The scalar/site/geometric cube uses the actual comparisons in the coefficient data.
Source: blueprint latest, coefficient-extension proof, site transport paragraph.
(blueprint: lem-sf-coefficient-site-pull-cube).
Proof: normalize the prescribed pro-etale scalar/pullback isomorphism by its
restriction/direct-image mate. The established etale/pro-etale scalar pullback
cube then gives the assertion; the site/pullback comparisons agree term by term. -/
theorem coefficient_site_pull_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y X : Scheme.{u}} (g : Y ⟶ X) (M : Cat A X) :
    (Sites.proScalarPull φ g).hom.app ((Sites.nu A X).obj M) ≫
        (Sites.scalar true φ Y).map ((Sites.sitePull A g).hom.app M) ≫
        (Sites.scalarSite φ Y).hom.app ((Sites.pull A g).obj M) =
      (Sites.proPull B g).map ((Sites.scalarSite φ X).hom.app M) ≫
        (Sites.sitePull B g).hom.app ((Sites.scalar false φ X).obj M) ≫
        (Sites.nu B Y).map ((Sites.scalarPull φ g).hom.app M) := by
  rw [proScalarPull_eq_scalarPullbackProEtaleIso]
  simpa only [sitePull_eq, Sites.nu, Sites.scalar, Sites.scalarSite,
    Sites.proPull, Sites.pull, Sites.scalarPull, id_eq, Etale.scalarExtension] using
    ProEtale.etaleProEtale_scalar_pullback_cube φ g M

/-- Taking the four site adjunction mates preserves the scalar/pullback cube.
Source: blueprint latest, coefficient-extension proof, site transport paragraph.
(blueprint: lem-sf-coefficient-site-pull-cube).
Proof: invert the left-adjoint cube, then apply exchangeMate_cube to the four
comparison adjunctions. Their counit formulas are exactly rnuScalar and rnuPull.
No comparison counit is removed or assumed invertible. -/
theorem coefficient_rnu_pull_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y X : Scheme.{u}} (g : Y ⟶ X) (M : Sites.D true A X) :
    (Sites.pull B g).map (Sites.rnuScalar φ X M) ≫
        Sites.rnuPull B g ((Sites.scalar true φ X).obj M) ≫
        (Sites.rnu B Y).map ((Sites.proScalarPull φ g).hom.app M) =
      (Sites.scalarPull φ g).hom.app ((Sites.rnu A X).obj M) ≫
        (Sites.scalar false φ Y).map (Sites.rnuPull A g M) ≫
        Sites.rnuScalar φ Y ((Sites.proPull A g).obj M) := by
  have hc (N : Cat A X) :
      (Sites.nu B Y).map ((Sites.scalarPull φ g).inv.app N) ≫
          (Sites.sitePull B g).inv.app ((Sites.scalar false φ X).obj N) ≫
          (Sites.proPull B g).map ((Sites.scalarSite φ X).inv.app N) =
        (Sites.scalarSite φ Y).inv.app ((Sites.pull A g).obj N) ≫
          (Sites.scalar true φ Y).map ((Sites.sitePull A g).inv.app N) ≫
          (Sites.proScalarPull φ g).inv.app ((Sites.nu A X).obj N) := by
    have h := IsIso.inv_eq_inv.mpr (coefficient_site_pull_cube φ g N)
    simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
      Category.assoc] using h.symm
  have h := exchangeMate_cube
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X)
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) X)
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y)
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) Y)
    (Sites.pull A g) (Sites.proPull A g) (Sites.pull B g) (Sites.proPull B g)
    (Sites.sitePull A g) (Sites.scalarPull φ g) (Sites.proScalarPull φ g)
    (Sites.sitePull B g) (Sites.scalarSite φ X).inv (Sites.scalarSite φ Y).inv hc M
  simpa only [mate_app_eq_adjunct, Sites.rnuScalar, Sites.rnuPull,
    Functor.comp_obj, Functor.id_obj, Sites.scalar, Sites.rnu, id_eq] using h

end WeilConjectures.FiniteFreeCoefficients
