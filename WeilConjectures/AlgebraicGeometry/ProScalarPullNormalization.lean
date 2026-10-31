/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtensionData
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.ScalarPullbackComposition

/-! # Agreement of the two canonical pro-etale scalar pullback comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- The composite-adjunction comparison is the inverse scalar mate.
Source: Mathlib iterated mates and the defining fixed restriction/direct-image mate.
(blueprint: lem-sf-pro-scalar-pull-normalization).
Proof: transpose the inverse scalar mate under the scalar adjunctions. Its image is
restriction/pullback. A second transpose under the geometric adjunctions is exactly
the inverse fixed restriction/direct-image comparison. Iterated mates identify this
with conjugation under the composite adjunctions. Invert the isomorphisms and use
injectivity of the conjugation equivalence. No coefficient flatness is used. -/
theorem proScalarPull_eq_scalarPullbackProEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y X : Scheme.{u}} (f : Y ⟶ X) :
    Sites.proScalarPull φ f = ProEtale.scalarPullbackProEtaleIso φ f := by
  let a := ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let b := ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let y := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
  let z := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)
  let e := ProEtale.scalarPullbackProEtaleIso φ f
  let t := ProEtale.fixedScalarRestrictionDirectImage φ f
  have hs : (mateEquiv y z e.inv).natTrans =
      (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ f).hom := by
    change (mateEquiv y z)
      ((mateEquiv y z).symm
        (TwoSquare.mk _ _ _ _ (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ f).hom)) = _
    exact Equiv.apply_symm_apply _ _
  dsimp only [TwoSquare.natTrans] at hs
  have hc : conjugateEquiv (y.comp b) (a.comp z) e.inv = t.inv := by
    rw [← iterated_mateEquiv_conjugateEquiv y z a b e.inv, hs]
    rfl
  have hi : conjugateIsoEquiv (y.comp b) (a.comp z) e.symm = t.symm := Iso.ext hc
  have hinv := congrArg Iso.inv hi
  have he : conjugateIsoEquiv (a.comp z) (y.comp b) e = t := Iso.ext hinv
  apply (conjugateIsoEquiv (a.comp z) (y.comp b)).injective
  change conjugateIsoEquiv (a.comp z) (y.comp b)
    ((conjugateIsoEquiv (a.comp z) (y.comp b)).symm t) = _
  rw [Equiv.apply_symm_apply]
  exact he.symm

private theorem pro_inverse_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Y X : Scheme.{u}} (f : Y ⟶ X) (N : Sites.D true A X) :
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)).unit.app
        ((Sites.proPull A f).obj N) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        ((ProEtale.scalarPullbackProEtaleIso φ f).inv.app N) =
    (Sites.proPull A f).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)).unit.app N) ≫
      (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ f).hom.app
        ((Sites.scalar true φ X).obj N) := by
  exact (unit_mateEquiv_symm
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ))
    (TwoSquare.mk _ _ _ _ (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ f).hom) N).symm

/-- The pro-etale comparison respects composition of geometric inverse images.
Source: Stacks 0D6D and the restriction/pullback compositor.
(blueprint: lem-sf-pro-scalar-pull-normalization).
Proof: transpose the restriction/pullback composition equation under the three
scalar adjunctions. Naturality of their units gives the reverse comparison
composition equation. Cancel its invertible factors to recover the forward one.
The preceding normalization identifies the comparison with the one used by Sites. -/
theorem pro_scalarPullback_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y T X : Scheme.{u}} (v : T ⟶ X) (j : Y ⟶ T)
    (N : Sites.D true A X) :
    (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} B) j v).hom.app
        ((Sites.scalar true φ X).obj N) ≫
      (Sites.proPull B j).map ((Sites.proScalarPull φ v).hom.app N) ≫
      (Sites.proScalarPull φ j).hom.app ((Sites.proPull A v).obj N) =
    (Sites.proScalarPull φ (j ≫ v)).hom.app N ≫
      (Sites.scalar true φ Y).map
        ((ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j v).hom.app N) := by
  simp only [proScalarPull_eq_scalarPullbackProEtaleIso]
  let S (T : Scheme.{u}) := Sites.scalar true φ T
  let U (T : Scheme.{u}) := Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ
  let F {T R : Scheme.{u}} (g : T ⟶ R) := Sites.proPull A g
  let P {T R : Scheme.{u}} (g : T ⟶ R) := Sites.proPull B g
  let r {T R : Scheme.{u}} (g : T ⟶ R) := (ProEtale.scalarPullbackProEtaleIso φ g).inv
  let d {T R : Scheme.{u}} (g : T ⟶ R) :=
    (ProEtale.leftDerivedUpperStarRestrictScalarsIso φ g).hom
  let cA := ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j v
  let cB := ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} B) j v
  have hr := reverseComposition (S X) (S T) (S Y) (U X) (U T) (U Y)
    (Adjunction.ofIsRightAdjoint _) (Adjunction.ofIsRightAdjoint _)
    (Adjunction.ofIsRightAdjoint _) (F v) (F j) (F (j ≫ v))
    (P v) (P j) (P (j ≫ v)) (r v) (r j) (r (j ≫ v))
    (d v) (d j) (d (j ≫ v)) cA cB N
    (pro_inverse_unit φ v N) (pro_inverse_unit φ j ((F v).obj N))
    (pro_inverse_unit φ (j ≫ v) N)
    (ProEtale.leftDerivedUpperStarRestrictScalarsIso_comp_hom_app φ j v ((S X).obj N))
  apply (cancel_epi ((ProEtale.scalarPullbackProEtaleIso φ (j ≫ v)).inv.app N)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% hr]
  simp only [r, F, P, cA, S, Functor.comp_obj,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

end WeilConjectures.FiniteFreeCoefficients
