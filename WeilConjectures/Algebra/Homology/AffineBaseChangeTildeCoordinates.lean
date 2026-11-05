/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde

/-! # Explicit coordinates for affine base-change cohomology

Source: Stacks Project, Tags 0DJ8, 06Y6 and 01I9.
(blueprint: def-pc-affine-base-change-tilde-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

/-- Exact tilde preserves zero morphisms. Source: Stacks, Tag 01I9.
(blueprint: def-pc-affine-base-change-tilde-coordinates). -/
@[instance] theorem affineBaseChangeTilde_preservesZero (A : Type u) [CommRing A] :
    (@id (ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace))
        (tilde.functor (.of A))).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ tilde.map_zero⟩

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Extend the tensor-algebra source cohomology to the actual upper-left ring.
Source: Stacks, Tag 0DJ8, displayed affine cohomology map.
(blueprint: def-pc-affine-base-change-tilde-coordinates). -/
def affineBaseChangeTildeModule
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D) (i : ℤ) : ModuleCat.{u} D :=
  (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (m.cohomology i)

/-- The actual module arrow is the tensor comparison followed by canonical target
coordinates. Source: Stacks, Tag 0DJ8, affine proof.
(blueprint: def-pc-affine-base-change-tilde-coordinates).
The equality hφ transports the extended complex along the specified ring map;
no module is chosen from a mere existence theorem. -/
def affineBaseChangeTildeModuleMap
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (φ : A →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (i : ℤ) (V : ModuleCat.{u} D)
    (b : (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M).homology i ≅ V)
    : affineBaseChangeTildeModule R A B D M m i ⟶ V :=
  m.localizedComparison i ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i).map
      (eqToHom (by rw [hφ] :
        ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
          (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj M =
        ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≫ b.hom

end AlgebraicGeometry
