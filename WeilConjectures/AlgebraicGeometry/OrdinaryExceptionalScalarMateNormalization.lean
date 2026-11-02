/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianDerivedExchangePlusCompatibility

/-! Scalar-adjunction normalization of the proper coefficient comparison.
Source: Zheng, Construction 2.26 and scalar adjunction compatibility
(blueprint: lem-sfb-ordinary-exceptional-scalar-mate-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

private theorem ordinaryScalarReverseOfMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {sx : A ⥤ B} {rx : B ⥤ A} (ax : sx ⊣ rx)
    {st : C ⥤ D} {rt : D ⥤ C} (at' : st ⊣ rt)
    {f : A ⥤ C} {rf : C ⥤ A} (af : f ⊣ rf)
    {g : B ⥤ D} {rg : D ⥤ B} (ag : g ⊣ rg)
    (e : rx ⋙ f ≅ g ⋙ rt) (δ : rg ⋙ rx ≅ rt ⋙ rf)
    (hδ : (mateEquiv ag af (TwoSquare.mk _ _ _ _ e.hom)).natTrans = δ.hom) :
    ((mateEquiv ax at').symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans =
      ((conjugateIsoEquiv (af.comp at') (ax.comp ag)).symm δ.symm).inv := by
  apply (mateEquiv ax at').injective
  apply (mateEquiv ag af).injective
  rw [Equiv.apply_symm_apply]
  apply TwoSquare.ext
  intro M
  have h := iterated_mateEquiv_conjugateEquiv ax at' af ag
    (TwoSquare.mk _ _ _ _
      ((conjugateIsoEquiv (af.comp at') (ax.comp ag)).symm δ.symm).inv)
  dsimp only [TwoSquare.mk, TwoSquare.natTrans] at h hδ
  rw [h, hδ]
  simp only [conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv]
  erw [Equiv.apply_symm_apply]

/-- The scalar-adjunction mate of the canonical direct-image comparison is the inverse
restriction/direct-image comparison.

Source: Zheng, Construction 2.26; the scalar/pullback normalization of
`scalarPullbackIso_inv_mate_restriction`
(blueprint: lem-sfb-ordinary-exceptional-scalar-mate-normalization).

Proof: express scalarMate as the geometric mate of scalarPullbackIso. The inverse
scalar mate of scalarRestrictionPullbackIso is scalarPullbackIso.inv by the normalized
scalar/pullback theorem. Apply the iterated-square-mates identity to the geometric
adjunctions and the scalar adjunctions. It identifies the scalar mate of scalarMate
with the inverse geometric mate of scalarRestrictionPullbackIso, which is precisely
the inverse of scalarRestrictionDirectImageMap. Substituting q.hom = scalarMate gives
the stated identity, retaining the chosen units and counits. -/
theorem ordinaryExceptional_scalarMate_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    [IsIso (scalarRestrictionDirectImageMap φ p)]
    (q : (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor ⋙ scalarExtension φ Y ≅
      scalarExtension φ Z ⋙ (lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctor)
    (hq : q.hom = scalarMate φ p) :
    (mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ))
      (TwoSquare.mk _ _ _ _ q.hom)).natTrans = inv (scalarRestrictionDirectImageMap φ p) := by
  let az := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
  let ay := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p
  let b := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p
  let δ := asIso (scalarRestrictionDirectImageMap φ p)
  let e := (conjugateIsoEquiv (a.comp az) (ay.comp b)).symm δ.symm
  have hr := ordinaryScalarReverseOfMate ay az a b (scalarRestrictionPullbackIso φ p) δ rfl
  have he : (scalarPullbackIso φ p).inv = e.inv := by
    rw [(scalarPullbackIso_inv_mate_restriction φ p).1]
    exact hr
  have hes : (scalarPullbackIso φ p).symm = e.symm := Iso.ext he
  have heh : (scalarPullbackIso φ p).hom = e.hom :=
    congrArg (fun i ↦ i.inv) hes
  rw [hq]
  change (mateEquiv az ay (mateEquiv a b
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ p).hom))).natTrans = δ.inv
  rw [iterated_mateEquiv_conjugateEquiv, heh]
  change conjugateEquiv (a.comp az) (ay.comp b) e.hom = δ.inv
  change ((conjugateIsoEquiv (a.comp az) (ay.comp b)) e).hom = δ.inv
  simp [e]

end AlgebraicGeometry.Etale
