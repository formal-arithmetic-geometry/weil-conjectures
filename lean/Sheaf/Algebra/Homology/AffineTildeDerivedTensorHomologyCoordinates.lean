/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Algebra.Homology.AffineTildeDerivedTensorMate

/-! # Homology coordinates of the raw affine tensor comparison

Source: Stacks Project, Tags 0DJ8, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-derived-tensor-homology-coordinates). -/

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

/-- Applying homology to the raw tensor counit gives precisely the module
comparison, coefficient homology map and normalized ordinary pushforward map.
This statement contains no geometric base-change map or pullback representative.
Source: Stacks Project, Tags 06Y6, 06Z0, 0AVW and 0DJ8, equation-bc.
(blueprint: lem-pc-affine-tilde-derived-tensor-homology-coordinates).

Proof: Expand affineTildeDerivedTensorSourceIso. Naturality of the exact-tilde
homology isomorphism moves m.counit past this comparison. On the localized
ordinary scalar-extension complex its comparison is the composite of the exact
homology isomorphism and the Q/homology isomorphism. Substitute m.comparison_eq
for the counit followed by m.ordinaryIso. Apply functoriality of homology to the
remaining factors of affineTildeTensorCoefficientComplexMap. Naturality of exact
restriction-of-scalars homology moves its isomorphism past ordinaryToLocalized;
compatibility with composition of exact functors cancels the intermediate
restriction comparisons. The homology of the identity-on-carriers scalar iso
is rho.inv on homology, and that of the equality transport is z0. Naturality of
exact tilde moves these maps past its homology comparison. The remaining
Q/homology comparison, termwise affine pushforward comparison and derived unit
are exactly affineTildePushforwardCohomologyMap. Reassociate to obtain the stated
identity. This uses no K-flatness, quasi-coherence, boundedness or invertibility
of the module comparison. The zero complex and zero rings are included. -/
theorem affineTildeDerivedTensorToPushforward_homology
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ) (i : ℤ) :
    let α := algebraMap (A ⊗[R] B) D
    let j : B →+* A ⊗[R] B := Algebra.TensorProduct.includeRight.toRingHom
    let T := tilde.functor (.of B)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
    let C := (((ModuleCat.extendScalars (α.comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj M)
    let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    let cE := m.comparison i ≫ HomologicalComplex.homologyMap m.ordinaryToLocalized i ≫
      ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom
    let ρ := ModuleCat.restrictScalarsComp' j α ψ hψ.symm
    let s := (ModuleCat.restrictScalars j).map cE ≫ ρ.inv.app (C.homology i)
    let z₀ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i).map
      (eqToHom (by dsimp only [C, α]; rw [hφ] : C = Cg))
    (affineTildeDerivedTensorSourceIso R A B D M m i).hom ≫
        H.map (affineTildeDerivedTensorToPushforward R A B D M m φ ψ hφ hψ) =
      T.map s ≫ T.map ((ModuleCat.restrictScalars ψ).map z₀) ≫
        affineTildePushforwardCohomologyMap D B ψ Cg i := by sorry

end AlgebraicGeometry
