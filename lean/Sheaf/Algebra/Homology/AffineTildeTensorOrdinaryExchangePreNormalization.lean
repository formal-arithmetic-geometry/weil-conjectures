/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison
public import Sheaf.Algebra.Homology.AffineBaseChangeTildeRepresentative
import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
import Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.TensorPullbackTilde

/-! The derived equality before target-map expansion and direct-image reassociation. -/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
local instance preNormTildeAdditive (A : Type u) [CommRing A] :
    (affineTildeFunctor A).Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
local instance preNormPushforwardAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pushforward f).Additive := ⟨fun {_ _} {_ _} ↦ rfl⟩
local instance preNormPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.tensorPullback f).Additive :=
  SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f

/-- The termwise pushforward comparison used in the target-map expansion.
Source: Stacks, Tag 01I9.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization). -/
def affineTildePushforwardComplexMap
    (D B : Type u) [CommRing D] [CommRing B] (ψ : B →+* D)
    (C : CochainComplex (ModuleCat.{u} D) ℤ) :
    let P := RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom
    ((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (P.mapHomologicalComplex (.up ℤ)).obj
        (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj C) := by
  let σ := affineTildePushforwardComparison D B ψ
  let P := RingedSpace.moduleDirectImage
    (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom
  let : P.Additive := RingedSpace.moduleDirectImage_additive_proof _
  exact { f := fun i ↦ σ.hom.app (C.X i)
          comm' := fun i j _ ↦ (σ.hom.naturality (C.d i j)).symm }

/-- The affine exchange calculation before expanding the target coefficient map.
Source: Stacks Project, Tags 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange-prenormalization).
Proof: transpose the ordinary base-change mate under tensor pullback along f'.
The pullback/tilde comparisons send the unit to 1 tensor q, while the affine
pushforward comparison uses the same tilde unit, sections restriction and counit.
Thus both transposed maps send b tensor q to psi(b) tensor q. The hypothesis hk
identifies them on these generators. Tensor induction and complex extensionality
prove the chain-map equality. Pass it through the homotopy quotient and localization.
Naturality of the right-derived unit then moves the inverse tensor/tilde comparison
to the final direct image. This proves the displayed equation before cancellation
against the invertible derived pullback counit; no such invertibility is assumed
here. Zero complexes and zero rings use the same generator calculation. -/
theorem affineTildeTensorOrdinaryExchange_preNormalization
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
 :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let p := Spec.map (CommRingCat.ofHom φ)
    let f' := Spec.map (CommRingCat.ofHom ψ)
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)
    let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    let P := ((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M
    let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
      Scheme.Modules.tensorPullback p
    let F' : SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) :=
      Scheme.Modules.pushforward f'
    let F := Scheme.Modules.pushforward f
    let G := Scheme.Modules.tensorPullback g
    let : E.Additive := preNormPullbackAdditive p
    let : G.Additive := preNormPullbackAdditive g
    let : F.Additive := preNormPushforwardAdditive f
    let : F'.Additive := preNormPushforwardAdditive f'
    let : (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
      ModuleCat.extendScalars_additive _
    let : (affineTildeFunctor A).Additive :=
      instAdditiveModuleCatCarrierModulesSpecOfFunctor
    let : (affineTildeFunctor D).Additive :=
      instAdditiveModuleCatCarrierModulesSpecOfFunctor
    let : (E ⋙ F').PreservesZeroMorphisms :=
      ⟨fun _ _ ↦ by
        rw [Functor.comp_map, E.map_zero]
        exact F'.map_zero _ _⟩
    let δ : (E.mapHomologicalComplex (.up ℤ)).obj P ≅
        ((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj C :=
      (Functor.mapHomologicalComplexCompIso
        (Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
          (CommRingCat.ofHom φ))) (.up ℤ)).app M
    let b₀ :
        (Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g) ⟶
          (E ⋙ F') :=
      { app := Scheme.Modules.moduleBaseChangeMap f f' g p hw
        naturality := fun _ _ z ↦
          Scheme.Modules.moduleBaseChangeMap_naturality f f' g p hw z }
    let b := (b₀.mapHomologicalComplex (.up ℤ)).app P
    let a := affineTildePushforwardComplexMap D B ψ C
    DerivedCategory.Q.map (affineTildeTensorOrdinarySourceIso R A B M).hom ≫
        DerivedCategory.Qh.map ((moduleHomotopyBaseChange f f' g p hw).app H) ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback p).mapHomotopyCategory (.up ℤ)).obj H) =
      (DerivedCategory.Q.map
          (((affineTildeFunctor B).mapHomologicalComplex (.up ℤ)).map k) ≫
        DerivedCategory.Q.map a ≫
        (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((affineTildeFunctor D).mapHomologicalComplex (.up ℤ)).obj C))) ≫
        (schemeDerivedDirectImage f').map
          (DerivedCategory.Q.map (affineBaseChangeTildeComplexIso A D φ M).inv) := by
  sorry

end AlgebraicGeometry
