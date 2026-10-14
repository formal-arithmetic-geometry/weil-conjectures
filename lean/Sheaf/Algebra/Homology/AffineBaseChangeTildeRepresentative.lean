/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization

/-! # AffineBaseChangeTildeRepresentative

Source: Stacks Project, Tag 0DJ8.
(blueprint: def-pc-affine-base-change-tilde-representative-iso). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The actual tilde representative of affine derived pullback.
Source: Stacks Project, Tags 01I9 and 08DW.
(blueprint: def-pc-affine-base-change-tilde-representative-iso).
The tensor-pullback comparison is unit-normalized. The other two factors are
respectively the inverse of the supplied derived counit and the image of e. -/
def affineBaseChangeTildeRepresentativeIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    DerivedCategory.Q.obj (((affineTildeFunctor A').mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≅
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K := by
  let TA := affineTildeFunctor A
  let TB := affineTildeFunctor A'
  let : TA.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : TB.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let f := Spec.map (CommRingCat.ofHom φ)
  let P := (TA.mapHomologicalComplex (.up ℤ)).obj M
  let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f
  let : IsIso ((SingleComplexBaseChange.counit f).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hc
  let θ := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom φ))
  let θ' : TA ⋙ E ≅ ModuleCat.extendScalars φ ⋙ TB := θ
  let δ : (E.mapHomologicalComplex (.up ℤ)).obj P ≅
      (TB.mapHomologicalComplex (.up ℤ)).obj C :=
    (Functor.mapHomologicalComplexCompIso θ' (.up ℤ)).app M
  exact (DerivedCategory.Q.mapIso δ).symm ≪≫
    (asIso ((SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))).symm ≪≫
    (derivedPullback f).mapIso e


/-- The chosen pullback representative is compatible with transport from the identity
representative. Source: Stacks Project, Tag 08HY. This follows directly from its
three defining factors and functoriality of derived pullback. -/
theorem affineBaseChangeTildeRepresentativeIso_identity_hom
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    (affineBaseChangeTildeRepresentativeIso A A' φ
      (DerivedCategory.Q.obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)) M
      (Iso.refl _) hc).hom ≫ (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map e.hom =
      (affineBaseChangeTildeRepresentativeIso A A' φ K M e hc).hom := by
  dsimp only [affineBaseChangeTildeRepresentativeIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.refl_hom,
    Category.assoc]
  congr 1
  congr 1
  exact ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).map_comp
    (𝟙 _) e.hom).symm.trans
      (congrArg (derivedPullback (Spec.map (CommRingCat.ofHom φ))).map
        (Category.id_comp e.hom))

end AlgebraicGeometry
