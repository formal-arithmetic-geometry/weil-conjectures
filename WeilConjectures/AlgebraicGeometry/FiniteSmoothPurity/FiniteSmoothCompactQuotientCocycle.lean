/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste

/-! # FiniteSmoothCompactQuotientCocycle

A step of finite smooth quotient coherence. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem open_chain_inverse
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (M : DerivedCategoryModule A X) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} C) j).mapDerivedCategory.map
        ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).inv.app M) ≫
      (ExceptionalCoefficients.openIso ψ j).inv.app ((ordinaryScalar φ X).obj M) ≫
      (ordinaryScalar ψ Z).map ((ExceptionalCoefficients.openIso φ j).inv.app M) =
    (ExceptionalCoefficients.openIso (ψ.comp φ) j).inv.app M ≫
      (ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ
        (ψ.comp φ) rfl).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) := by
  let o (R : Type (u + 1)) [CommRing R] :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) j).symm
  let a (T : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
      (ρ : R →+* S) :=
    Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology ρ)
  have he {R S : Type (u + 1)} [CommRing R] [CommRing S] (ρ : R →+* S) :
      conjugateEquiv ((o R).comp (a Z ρ)) ((a X ρ).comp (o S))
        (ExceptionalCoefficients.openIso ρ j).inv =
          (scalarRestrictionPullbackIso ρ j).hom := by
    exact congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply
      (scalarRestrictionPullbackIso ρ j))
  have h := conjugateEquiv_paste (o A) (o B) (o C)
    (a X φ) (a Z φ) (a X ψ) (a Z ψ) (a X (ψ.comp φ)) (a Z (ψ.comp φ))
    (ExceptionalCoefficients.openIso φ j).inv
    (ExceptionalCoefficients.openIso ψ j).inv
    (ExceptionalCoefficients.openIso (ψ.comp φ) j).inv
    (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ (ψ.comp φ) rfl).inv
    (ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ (ψ.comp φ) rfl).inv
    (by
      rw [he, he, he]
      simp only [a, ProEtale.pbcFixedScalarExtensionComp,
        Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
      ext K : 2
      dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      rw [AlgebraicGeometry.Etale.scalarRestriction_chain φ ψ j K]
      simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.id_comp])
  exact congr_app h M

private theorem open_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (M : DerivedCategoryModule A X) :
    (ordinaryScalar ψ Z).map ((ExceptionalCoefficients.openIso φ j).hom.app M) ≫
      (ExceptionalCoefficients.openIso ψ j).hom.app ((ordinaryScalar φ X).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} C) j).mapDerivedCategory.map
        ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app M) =
    (ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ
        (ψ.comp φ) rfl).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (ExceptionalCoefficients.openIso (ψ.comp φ) j).hom.app M := by
  let a := ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ (ψ.comp φ) rfl
  let b := ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ (ψ.comp φ) rfl
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} C) j).mapDerivedCategory
  let e := J.mapIso (a.symm.app M) ≪≫
    (ExceptionalCoefficients.openIso ψ j).symm.app ((ordinaryScalar φ X).obj M) ≪≫
    (ordinaryScalar ψ Z).mapIso ((ExceptionalCoefficients.openIso φ j).symm.app M)
  let e' := (ExceptionalCoefficients.openIso (ψ.comp φ) j).symm.app M ≪≫
    b.symm.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M)
  have he : e = e' := Iso.ext (open_chain_inverse φ ψ j M)
  have h := congrArg Iso.inv he
  simpa only [e, e', a, b, J, Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
    Functor.mapIso_inv, Category.assoc] using h

private theorem proper_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (M : DerivedCategoryModule A Z) :
    (ProEtale.pbcFixedScalarExtensionComp Y.smallEtaleTopology φ ψ
        (ψ.comp φ) rfl).hom.app
          ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj M) ≫
      (scalarMate (ψ.comp φ) p).app M =
    (ordinaryScalar ψ Y).map ((scalarMate φ p).app M) ≫
      (scalarMate ψ p).app ((ordinaryScalar φ Z).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} C) p).rightDerivedFunctor.map
        ((ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ
          (ψ.comp φ) rfl).hom.app M) := by
  have h := finiteCoefficientDirectImageMap_coefficientChain φ ψ p M
  simp only [AlgebraicGeometry.Etale.finiteCoefficientDirectImageMap_eq_mate] at h
  change (scalarMate (ψ.comp φ) p).app M = _ at h
  rw [h]
  simp only [Iso.hom_inv_id_app_assoc, ordinaryScalar, scalarMate]

private theorem compact_chain
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (ProEtale.pbcFixedScalarExtensionComp Y.smallEtaleTopology φ ψ χ hχ).hom.app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
      ExceptionalCoefficients.compactSupportMap χ c M =
    (ordinaryScalar ψ Y).map (ExceptionalCoefficients.compactSupportMap φ c M) ≫
      ExceptionalCoefficients.compactSupportMap ψ c ((ordinaryScalar φ X).obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
        ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ hχ).hom.app M) := by
  subst χ
  have hp := proper_chain φ ψ c.g
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  have ho := open_chain φ ψ c.i M
  have hn := (scalarMate ψ c.g).naturality
    ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
  have hmap := congrArg
    (fun h ↦ (lowerStar (ModuleCat.{u + 1} C) c.g).rightDerivedFunctor.map h) ho
  dsimp only [ordinaryScalar] at hp ho hn hmap ⊢
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Functor.map_comp] at hmap
  dsimp only [ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_obj, Functor.comp_map]
  rw [← Category.assoc, hp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hmap]
  rw [← reassoc_of% hn]

end AlgebraicGeometry.Etale.FiniteSmoothPurity
