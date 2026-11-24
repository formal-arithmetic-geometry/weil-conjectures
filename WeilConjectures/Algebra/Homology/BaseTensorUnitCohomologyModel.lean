/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizationModelSemilinear
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.MixedTotalTensorScalarExtension
import WeilConjectures.Algebra.Homology.BalancedTensorUnitModelComparison

/-! # Coefficient-unit map computed by a balanced complex

## References

* Stacks Project, Tags 064L and 06Y6 (balanced computation of the derived tensor product)
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology
variable (R A Aq B D : Type u)
  [CommRing R] [CommRing A] [CommRing Aq] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra A Aq] [Algebra R Aq]
  [IsScalarTower R A Aq]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- The coefficient-unit map is computed by a balanced complex, before any localization:
there are a complex `C` of `A`-modules and `A`-linear isomorphisms identifying the two derived
tensor cohomology models with the homology of `C` and of its extension to `Aq`, compatibly with
the unit map. No flatness of `Aq` is required. -/
theorem exists_baseTensorUnitCohomologyModel (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (uQ : (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q))
    (huQ : ∀ (j : ℤ) (x : Q.X j), uQ.f j x = (1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) :
    ∃ (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (e : (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeft (S := R) : A →ₐ[R] A ⊗[R] B).toRingHom).obj
          (L.cohomology i) ≅ C.homology i)
      (e' : (ModuleCat.restrictScalars
        ((Algebra.TensorProduct.includeLeft (S := R) : Aq →ₐ[R] Aq ⊗[R] B).toRingHom.comp
          (algebraMap A Aq))).obj (K.cohomology i) ≅
          ((restrict A Aq).obj ((extend A Aq).obj C)).homology i),
      ∀ x : L.cohomology i,
        e'.hom (localizationModelMap R A Aq B D i Q L K uQ x) =
          (HomologicalComplex.homologyMap
            (((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
              (.up ℤ)).unit.app C) i) (e.hom x) := by
  classical
  let E := (CochainComplex.singleFunctor (ModuleCat.{u} R) (0 : ℤ)).obj (ModuleCat.of R B)
  let Λ := flatResolution R
  let F := Λ.resolutionFunctor.obj E
  let f := Λ.resolutionNatTrans.app E
  have hf : QuasiIso f := inferInstance
  have hF := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le E
  obtain ⟨θ, hθ⟩ := exists_mixedTotalTensor_scalarExtension R A Aq Q F
  obtain ⟨e, eq, he⟩ :=
    exists_balancedTensorUnitModelComparison R A Aq B D i Q L K uQ huQ F f hf hF θ hθ
  let C := ((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) i
  let t := H.mapIso ((restrict A Aq).mapIso θ)
  refine ⟨C, e, eq ≪≫ t.symm, ?_⟩
  intro x
  have hx := he x
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  change t.inv (eq.hom (localizationModelMap R A Aq B D i Q L K uQ x)) = _
  rw [hx, HomologicalComplex.homologyMap_comp]
  change t.inv (t.hom
    ((HomologicalComplex.homologyMap
      (((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
        (.up ℤ)).unit.app C) i) (e.hom x))) = _
  exact congrArg (fun k ↦ k
    ((HomologicalComplex.homologyMap
      (((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
        (.up ℤ)).unit.app C) i) (e.hom x))) t.hom_inv_id

end RingTensorCohomology
