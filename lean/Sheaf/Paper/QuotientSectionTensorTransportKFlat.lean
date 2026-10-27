/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData
import Sheaf.Paper.IntegralResidueDerivedMonoidal

/-! # Flat-term representative conjugation for quotient section tensors -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The conjugation equation on flat-term K-flat representatives.
Source: Stacks 06YY, 07A4 and 07A6; parent proof steps 6--8.
(blueprint: lem-sfb-quotient-section-tensor-transport-condition).

Proof: choose flat-term K-flat representatives for the two derived inputs.  Expand the
normalized section tensor equation supplied by `hbarB`, substitute the normalized scalar
counit equation `hc` and the normalized internal tensorator equation `hb`, and cancel the
invertible localization and comparison maps.  The remaining representative equation is
exactly the displayed conjugation equation.  All maps are natural in both representatives,
so the calculation is independent of the chosen resolutions. -/
theorem section_tensor_transport_kflat (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (hbarB : SectionTensorNormalized a T c barB) :
    ∀ (P Q : CochainComplex (Modules Λ T) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      (derivedFunctor Λ' T).map (b.hom.app (DerivedCategory.Q.obj P,
          DerivedCategory.Q.obj Q)) ≫
          (tensorComparison Λ' T).hom.app ((D a T).obj (DerivedCategory.Q.obj P),
            (D a T).obj (DerivedCategory.Q.obj Q)) =
        c.derived.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q) ≫
          c.model.T.map ((tensorComparison Λ T).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
          barB.hom.app ((derivedFunctor Λ T).obj (DerivedCategory.Q.obj P),
            (derivedFunctor Λ T).obj (DerivedCategory.Q.obj Q)) ≫
          (tensor Λ' T).map (Prod.mkHom (c.derived.inv.app (DerivedCategory.Q.obj P))
            (c.derived.inv.app (DerivedCategory.Q.obj Q))) := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
