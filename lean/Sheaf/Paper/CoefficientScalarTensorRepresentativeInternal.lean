/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Paper.CoefficientScalarTensorRepresentativeEquation
public import Sheaf.Paper.CoefficientScalarTensorRepresentativeHypotheses
import Sheaf.Paper.CoefficientScalarTensorRepresentativePasting
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Sheaf.Paper.SectionDerivedRealization
import Sheaf.Algebra.Homology.KFlatTotalTensorModel

/-! # Internal-complex scalar tensor representatives

The first strict substep proves the signed representative equation when both
section complexes are termwise images of internal complexes. The hypotheses in
`CoefficientScalarTensorRepresentativeBasicData` are exactly the normalized ordinary,
scalar and derived comparison formulas needed for this restricted case.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-internal)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap internalScalarExtension
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  ModuleRingedComparison.totalComparison ModuleRingedComparison.ordinaryTensorComparison
  Localization.Monoidal.tensorBifunctor

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

/-- On reconstructed internal complexes, the normalized ordinary generator equation,
its signed totalization, and the assumed derived tensor square give the representative
identity. This is strictly the internal-image case of the main section-complex claim.

Source: Stacks Project, Cohomology on Sites, Tag 07A4, constituent total-complex maps.
Use the proved ordinary and total-complex squares and the derived tensor counit
square. The tensor of the two section models is K-flat with flat terms; transport
these properties across totalComparison and apply hscalar to the tensor model.
Normalize both localization tensor maps, paste the naturality, scalar and tensor
squares, and cancel the composite comparison isomorphism.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-internal). -/
theorem coefficientScalarTensorRepresentative_internal
    (Z : Scheme.{u})
    (d : CoefficientScalarTensorRepresentativeBasicData a Z)
    (h : CoefficientScalarTensorRepresentativeHypotheses a Z d) :
    ∀ (P Q : CochainComplex (ModuleRingedComparison.internalModules R Z) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z)
        (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
          (.up ℤ)).obj P) →
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z)
        (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
          (.up ℤ)).obj Q) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z)
        ((ModuleRingedComparison.equivalence R Z).functor.obj (P.X n))) →
      (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
        (R := ModuleRingedComparison.ring R Z)
        ((ModuleRingedComparison.equivalence R Z).functor.obj (Q.X n))) →
      coefficientScalarTensorRepresentativeEquation a Z d
        (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
          (.up ℤ)).obj P)
        (((ModuleRingedComparison.equivalence R Z).functor.mapHomologicalComplex
          (.up ℤ)).obj Q) := by
  intro P Q hp hq hpf hqf
  let ER := (ModuleRingedComparison.equivalence R Z).functor
  let ERc := ER.mapHomologicalComplex (.up ℤ)
  let EP := ERc.obj P
  let EQ := ERc.obj Q
  let r : ERc.obj (P ⊗ Q) ≅ EP ⊗ EQ := ModuleRingedComparison.totalComparison R Z P Q
  have ht := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (ModuleRingedComparison.ring R Z) EP EQ hp hq hpf hqf
  have hk : CochainComplex.IsKFlatIndependentCoefficients
      (R := ModuleRingedComparison.ring R Z) (ERc.obj (P ⊗ Q)) :=
    ModuleRingedComparison.independent_kflat_of_iso R Z r.symm ht.1
  have hfl (n : ℤ) : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (C := Z.ProEt) (J := Scheme.ProEt.topology Z)
      (R := ModuleRingedComparison.ring R Z) (ER.obj ((P ⊗ Q).X n)) := by
    have hf := SheafOfModules.flat_to_cat (ModuleRingedComparison.ring R Z) _ (ht.2.1 n)
    have hf' := (ObjectProperty.flat (A := ModuleRingedComparison.modules R Z)).prop_of_iso
      ((HomologicalComplex.eval _ (.up ℤ) n).mapIso r.symm) hf
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (ModuleRingedComparison.ring R Z) _).symm hf'.2
  exact coefficientScalarTensorRepresentative_paste a Z d h P Q
    (h.hscalar P hp hpf) (h.hscalar Q hq hqf) (h.hscalar (P ⊗ Q) hk hfl)

end AlgebraicGeometry.ProEtale.CondensedRing
