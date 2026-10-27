/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData
import Sheaf.Paper.IntegralResidueDerivedMonoidal

/-! # Derived total normalization of the quotient section tensor comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

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

/-- The pure section comparison extends to the normalized signed total on K-flat pairs.
Source: Stacks 06YS, 07A4 and 0G7D; parent proof steps 3--5.
(blueprint: lem-sfb-quotient-section-tensor-transport-normalized-total).

Proof: totalize the balancing map with the Koszul sign on each bidegree.  The
coproduct inclusions give the summand equations, and the localization counit square
gives the derived comparison equation. -/
theorem section_tensor_transport_normalized_total (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
        (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
          (curriedTensor (modules Λ' T)))
    (he : ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
      (n : N.val.obj W) (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
          (sectionScalarElement a T c (M ⊗ N) W
            (sectionPureTensor Λ T M N W m n) s) =
        sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
          (sectionScalarElement a T c M W m 1)
          (sectionScalarElement a T c N W n s)) :
    ∀ P Q : CochainComplex (modules Λ T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := ring Λ T) Q →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (P.X i)) →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
        (R := ring Λ T) (Q.X i)) →
      ∃ g : (c.model.E.mapHomologicalComplex (.up ℤ)).obj
            ((totalTensor Λ T).obj (P, Q)) ⟶
          (totalTensor Λ' T).obj
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q),
        (∀ (i j k : ℤ) (h : i + j = k),
          c.model.E.map
              (CochainComplex.ιMapBifunctor P Q (curriedTensor (modules Λ T))
                i j k h) ≫ g.f k =
            (e.app (P.X i)).app (Q.X j) ≫
              CochainComplex.ιMapBifunctor
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P)
                ((c.model.E.mapHomologicalComplex (.up ℤ)).obj Q)
                (curriedTensor (modules Λ' T)) i j k h) ∧
        barB.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            (tensor Λ' T).map (Prod.mkHom (c.model.ε.app P) (c.model.ε.app Q)) ≫
            (qTensor Λ' T).app
              ((c.model.E.mapHomologicalComplex (.up ℤ)).obj P,
                (c.model.E.mapHomologicalComplex (.up ℤ)).obj Q) =
          c.model.T.map ((qTensor Λ T).app (P, Q)) ≫
            c.model.ε.app ((totalTensor Λ T).obj (P, Q)) ≫ DerivedCategory.Q.map g := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
