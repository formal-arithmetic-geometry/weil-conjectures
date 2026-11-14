/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import WeilConjectures.AlgebraicGeometry.AffineOpenPushforwardAcyclic
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Acyclicity after pullback of an affine-open direct image

## References

* Stacks Project, Tag 02KG
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Arbitrary base change of an affine-open direct image is acyclic over the new affine base
(Stacks, Tag 02KG). -/
theorem affine_open_pushforward_pullback_rightAcyclic
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsSeparated f] (g : Spec B ⟶ Spec A)
    (W : X.Opens) (hW : IsAffineOpen W)
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    (RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).rightAcyclic
      ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj
        ((Scheme.Modules.pushforward W.ι).obj (G.restrict W.ι))) := by
  let p := pullback.fst f g
  let W' := p ⁻¹ᵁ W
  let pW := p ∣_ W
  have : IsAffine W.toScheme := hW
  have : IsAffineHom (W.ι ≫ f) := inferInstance
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι f
  have : IsAffineHom g := inferInstance
  have : IsAffineHom p := MorphismProperty.pullback_fst _ _ ‹IsAffineHom g›
  have hW' : IsAffineOpen W' := hW.preimage p
  let eP (Y Z : Scheme.{u}) (h : Y ⟶ Z) :
      Scheme.Modules.tensorPullback h ≅ Scheme.Modules.pullback h :=
    Adjunction.leftAdjointUniq (Scheme.Modules.nonempty_tensorPullbackAdjunction h).some
      (Scheme.Modules.pullbackPushforwardAdjunction h)
  have hPG : ((Scheme.Modules.tensorPullback p).obj G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pullback f g).ringCatSheaf).prop_of_iso
      ((eP _ _ p).app G).symm (Scheme.Modules.isQuasicoherent_pullback p G)
  let eR : ((Scheme.Modules.tensorPullback p).obj G).restrict W'.ι ≅
      (Scheme.Modules.tensorPullback pW).obj (G.restrict W.ι) :=
    (Scheme.Modules.restrictFunctor W'.ι).mapIso ((eP _ _ p).app G) ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback W'.ι).app
        ((Scheme.Modules.pullback p).obj G) ≪≫
      (Scheme.Modules.pullbackComp W'.ι p).app G ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι p W).symm).app G ≪≫
      (Scheme.Modules.pullbackComp pW W.ι).symm.app G ≪≫
      (Scheme.Modules.pullback pW).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app G).symm ≪≫
      ((eP _ _ pW).app (G.restrict W.ι)).symm
  have hbase := (Scheme.Modules.affinePushforward_baseChange W.ι W'.ι p pW
    (isPullback_morphismRestrict p W) (G.restrict W.ι)).2
  let eB := asIso (Scheme.Modules.moduleBaseChangeMap W.ι W'.ι p pW
    (isPullback_morphismRestrict p W).w (G.restrict W.ι))
  apply (RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).rightAcyclic.prop_of_iso
    (eB ≪≫ (Scheme.Modules.pushforward W'.ι).mapIso eR.symm).symm
  exact affine_open_pushforward_rightAcyclic (pullback.snd f g) W' hW'
    ((Scheme.Modules.tensorPullback p).obj G)

end AlgebraicGeometry
