/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization
import all WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization

/-! # Ordinary affine exchange in tensor coordinates

## References

* Stacks Project, Tag 06Y6
* Stacks Project, Tag 08HY
* Stacks Project, Tag 01I9
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

local instance (priority := 2000) ordinaryCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance (priority := 2000) ordinaryCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance (priority := 2000) ordinaryCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))


local instance ordinaryExchangeTildeAdditive (C : Type u) [CommRing C] :
    (affinePushforwardTilde C).Additive := by
  constructor
  intro M N f g
  exact tilde.map_add (R := .of C) f g

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

local instance ordinaryExchangePullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f

/-- The ordinary coefficient map, affine pushforward comparison and derived unit.
This is a concrete map, independent of any derived scalar-extension model. -/
def affineTildeTensorOrdinaryTargetMap
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (φ : A →+* D) (ψ : B →+* D)
    (k : (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ⟶
      ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) :
    DerivedCategory.Q.{w}.obj (((affinePushforwardTilde B).mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M))) ⟶
    (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom ψ))).obj
      (DerivedCategory.Q.{w}.obj (((affinePushforwardTilde D).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))) := by
  let T := affinePushforwardTilde B
  let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let a := affineTildePushforwardComplexMap D B ψ Cg
  exact DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map k) ≫
    DerivedCategory.Q.map a ≫
    cast (by rfl) ((RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affinePushforwardTilde D).mapHomologicalComplex (.up ℤ)).obj Cg)))

/-- Ordinary exchange, in unit-normalized affine tensor coordinates, followed by
its right-derived unit. This is independent of any derived tensor model or counit. -/
theorem affineTildeTensorOrdinaryExchange
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (φ : A →+* D) (ψ : B →+* D)
    (hw : Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom ψ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (k : (((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex
          (.up ℤ)).obj M)) ⟶
      ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))
    (hk : ∀ (i : ℤ) (b : B) (q : M.X i),
      k.f i (b ⊗ₜ[R,algebraMap R B] q) = ψ b ⊗ₜ[A,φ] q)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := Spec.map (CommRingCat.ofHom φ)
    let f' := Spec.map (CommRingCat.ofHom ψ)
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)
    let t := affineBaseChangeTildeRepresentativeIso A D φ
      (DerivedCategory.Q.obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj M)) M (Iso.refl _) hc
    DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom ≫
        cast (by rfl) ((DerivedCategory.Qh.{w}
          (C := SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))).map
          ((moduleHomotopyBaseChange f f' g p hw).app H)) ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H) =
      affineTildeTensorOrdinaryTargetMap R A B D M φ ψ k ≫
        (schemeDerivedDirectImage f').map t.hom ≫
        (schemeDerivedDirectImage f').map
          (cast (by rfl) ((SingleComplexBaseChange.counit p).app H)) := by
  dsimp only
  have h := affineTildeTensorOrdinaryExchange_preNormalization R A B D M φ ψ hw k hk
  dsimp only at h
  rw [← (schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom ψ))).map_comp,
    affineBaseChangeTildeRepresentativeIso_counit A D φ M hc]
  simpa only [affineTildeTensorOrdinaryTargetMap, cast_eq, Category.assoc] using h


end AlgebraicGeometry
