/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentationData
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulUnitZeroIso
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientProjection
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicKoszulConstruction
import all WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality

/-! # Existence of the finite strict completed Koszul tensor augmentation

Source: Stacks Project, Tags 091N and 099M.
(blueprint: new-y2-completed-koszul-tensor-quotient-augmentation-exists).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

section TensorNaturality

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  (F : C ⥤ C ⥤ C) [F.PreservesZeroMorphisms]
  [∀ X, (F.obj X).PreservesZeroMorphisms]
  [∀ P Q : CochainComplex C ℤ, HomologicalComplex.HasMapBifunctor P Q F (.up ℤ)]

end TensorNaturality

end AlgebraicGeometry.Scheme
