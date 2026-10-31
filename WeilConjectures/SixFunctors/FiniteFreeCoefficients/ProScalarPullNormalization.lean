/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition

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

end WeilConjectures.FiniteFreeCoefficients
