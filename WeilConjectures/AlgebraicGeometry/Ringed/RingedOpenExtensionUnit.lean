/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import Mathlib.CategoryTheory.Adjunction.Triple

/-! # The ordinary ringed open-extension unit

Source: Stacks Project, Tags 03DI and 03DJ: extension from a subterminal slice.
(blueprint: lem-zl-ringed-open-extension-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

private theorem localizedUnit {X : Scheme.{u}} (U : X.ProEt)
    [IsOpenImmersion U.hom] (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    IsIso (SheafOfModules.localizedModuleAdjunctionIndependent R U).unit := by
  let A := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let b := SheafOfModules.overPushforwardOverAdj (R := A) U
  have hsub : ∀ W : X.ProEt, Subsingleton (W ⟶ U) := by
    intro W
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.hom).mp
    exact f.w.trans g.w.symm
  have : (Over.forget U).Full := by
    constructor
    intro V V' f
    exact ⟨Over.homMk f (@Subsingleton.elim _ (hsub V.left) _ _), rfl⟩
  have : IsIso (Over.forgetAdjStar U).unit := inferInstance
  have hb : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    change IsIso (N.val.presheaf.map ((Over.forgetAdjStar U).unit.app W.unop).op)
    infer_instance
  let triple : Adjunction.Triple _ _ _ :=
    ⟨SheafOfModules.localizedModuleAdjunctionIndependent R U, b⟩
  exact triple.isIso_unit_iff_isIso_counit.mpr hb

/-- The unit of ordinary extension by zero followed by ringed open pullback is invertible.
The coefficient sheaves and their inverse-image identification are arbitrary.

Source: Stacks Project, sites-modules.tex, Tags 03DI and 03DJ.
(blueprint: lem-zl-ringed-open-extension-unit).

Proof: an open immersion represents a subterminal object of the pro-etale site.
Thus the forgetful functor from its over-category is fully faithful, and its
forgetful/star adjunction unit is invertible. The counit of module restriction
followed by over-pushforward is sectionwise the image of this isomorphism, so it
is invertible. The extension/restriction/over-pushforward adjunction triple gives
invertibility of the localized extension unit. Its left adjoint is fully faithful.
The open-slice presentation expresses actual extension by zero as that functor
after an equivalence, hence it too is fully faithful. Its specified adjunction
therefore has invertible unit. This includes empty and identity opens and zero rings. -/
theorem proEtaleRingOpenAdjunction_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    (RX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (RU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj RX ≅ RU) :
    IsIso (Adjunction.ofIsRightAdjoint (proEtaleRingModulePullback j RX RU c)).unit := by
  obtain ⟨e, ⟨he⟩⟩ := proEtaleOpen_slicePresentation j RX RU c
  have : IsOpenImmersion (ProEt.mk j).hom := by
    change IsOpenImmersion j
    infer_instance
  let a := SheafOfModules.localizedModuleAdjunctionIndependent RX (ProEt.mk j)
  have : IsIso a.unit := localizedUnit (ProEt.mk j) RX
  have := a.fullyFaithfulLOfIsIsoUnit.full
  have := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : (proEtaleRingOpenExtension j RX RU c).Full := Functor.Full.of_iso he.symm
  have : (proEtaleRingOpenExtension j RX RU c).Faithful := Functor.Faithful.of_iso he.symm
  let b : proEtaleRingOpenExtension j RX RU c ⊣ proEtaleRingModulePullback j RX RU c :=
    Adjunction.ofIsRightAdjoint _
  exact b.unit_isIso_of_L_fully_faithful

end AlgebraicGeometry.Scheme
