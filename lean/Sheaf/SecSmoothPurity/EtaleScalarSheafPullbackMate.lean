/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection

/-! # Scalar adjunction normalization of ordinary etale pullback

Source: Stacks Tag 07A4; Steps 2--3 of lem-sfb-etale-proetale-scalar-mate.
(blueprint: lem-sp-etale-scalar-sheaf-pullback-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale

private theorem underived_mate
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)).natTrans =
        (lowerStarRestrictScalarsIso φ f).hom := by
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)
    (Sheaf.restrictCoextendScalarsAdj W.smallEtaleTopology φ)).injective
  change (mateEquiv (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)
    (Sheaf.restrictCoextendScalarsAdj W.smallEtaleTopology φ)
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom))).natTrans = _
  rw [iterated_mateEquiv_conjugateEquiv]
  simp only [upperStarRestrictScalarsIsoSheaf, Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, TwoSquare.mk]
  erw [Equiv.apply_symm_apply]
  ext M ⟨U⟩ x
  exact congrArg (fun t ↦ t.hom x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
      (M.obj.obj (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)))).symm


/-- The ordinary scalar/pullback comparison is the inverse of the scalar adjunction mate.
Source: Stacks Tag 07A4; Steps 2--3 of lem-sfb-etale-proetale-scalar-mate
(blueprint: lem-sp-etale-scalar-sheaf-pullback-mate).

Proof: transpose under the scalar and geometric adjunctions in either order. The
restriction/pullback square is defined by the restriction/coextension adjunction;
its geometric mate is the sectionwise restriction/direct-image identity, by the
coextension triangle equation. The iterated-mate identity therefore identifies the
inverse scalar mate with the composite-adjunction conjugate defining
scalarSheafPullbackIso. Injectivity of conjugation proves the equality. -/
theorem scalarSheafPullbackIso_inverseMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((mateEquiv (ProEtale.etaleSheafExtendScalarsAdjunction φ Y)
      (ProEtale.etaleSheafExtendScalarsAdjunction φ X)).symm
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)).natTrans =
      (scalarSheafPullbackIso φ f).inv := by
  apply (conjugateEquiv
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ Y).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
      (ProEtale.etaleSheafExtendScalarsAdjunction φ X))).injective
  rw [← iterated_mateEquiv_conjugateEquiv]
  rw [Equiv.apply_symm_apply]
  change (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIsoSheaf φ f).hom)).natTrans = _
  rw [underived_mate]
  simp only [scalarSheafPullbackIso, conjugateIsoEquiv_symm_apply_inv]
  rw [Equiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.Etale
