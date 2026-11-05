/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulCoefficientConeRealization
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorAugmentationComponent
import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.preservesZeroMorphisms_of_additive
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

attribute [local instance] completedKoszulCochainMonoidal
  completedKoszulCochainMonoidalStruct
attribute [local irreducible] completedAdicRing

@[irreducible] def koszulTensorUnitor
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (K P : CochainComplex (CompletedAdicModules T d) ℤ) :
    P ⊗ ((𝟙_ _) ⊗ K) ≅ P ⊗ K :=
  (tensorLeft P).mapIso (λ_ K)

@[irreducible] def quotientUnitIso
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Q : CompletedAdicModules T d) :
    ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj (𝟙_ _) ≅
      (HomologicalComplex.single _ (.up ℤ) 0).obj Q :=
  (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q (𝟙_ _)).symm ≪≫
    λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj Q)

@[irreducible] def quotientTensorIso
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (Q : CompletedAdicModules T d) (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    P ⊗ ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj (𝟙_ _) ≅
      ((tensorRight Q).mapHomologicalComplex (.up ℤ)).obj P :=
  (tensorLeft P).mapIso (quotientUnitIso T d Q) ≪≫
    CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q P

end AlgebraicGeometry.Scheme
