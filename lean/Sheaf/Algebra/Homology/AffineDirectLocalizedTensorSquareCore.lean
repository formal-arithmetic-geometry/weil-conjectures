/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.Algebra.Homology.AffineBaseChangeTildeCoordinates

import Sheaf.Algebra.Homology.DerivedTensorFirstLocalizationModels
import Sheaf.Algebra.Homology.DerivedTensorBaseSecondLocalizationModels

/-! Core derived localization and stalk comparison glue.
(blueprint: new-affine-direct-localized-tensor-square-core). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/--
For an explicitly supplied affine tilde complex `P`, the common localization model
produces the comparison isomorphism and its universal characterization. This is the
substantial derived localization and stalk glue step in the proof of the parent theorem.
Source: Stacks Project, Tag 0DJ8, together with Tags 06Y6 and 01I9.
(blueprint: new-affine-direct-localized-tensor-square-core).
-/
theorem affineDirectLocalizedTensorSquare_core
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ)
    (p : PrimeSpectrum A') :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let D : Type u := (Spec.structureSheaf A').presheaf.stalk p
      let κ := (StructureSheaf.toStalk A' p).hom
      letI : Algebra (A ⊗[R] R') D :=
        (κ.comp (algebraMap (A ⊗[R] R') A')).toAlgebra
      (n : ModuleCat.BaseDerivedTensorCohomologyModel R A R' M D) →
      let C := ((ModuleCat.extendScalars (κ.comp φg')).mapHomologicalComplex (.up ℤ)).obj M
      let U := affineBaseChangeTildeModule R A R' D M n i
      let hφ : (algebraMap (A ⊗[R] R') D).comp
          (algebraMap A (A ⊗[R] R')) = κ.comp φg' :=
        by
          change (κ.comp (algebraMap (A ⊗[R] R') A')).comp _ = _
          rw [RingHom.comp_assoc, hφg'] 
      let a := affineBaseChangeTildeModuleMap R A R' D M n (κ.comp φg') hφ i
        (C.homology i) (Iso.refl _)
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      let l :=
        (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i
      ∃ e : U ≅ (Arrow.mk l).left,
        ∀ τ : C ≅
            SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
          (∀ (j : ℤ) (x : M.X j),
            τ.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
              (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
                (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                  (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
          a ≫ HomologicalComplex.homologyMap τ.hom i = e.hom ≫ l := by sorry


end AlgebraicGeometry
