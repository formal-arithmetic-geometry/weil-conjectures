/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData
import Sheaf.Paper.IntegralResidueDerivedMonoidal

/-! # Ordinary normalization of the quotient section tensor comparison -/

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

/-- The underlying section comparison has the prescribed pure-tensor formula.
Source: Stacks 03EK, 03EL and 07A4; parent proof steps 1--3.
(blueprint: lem-sfb-quotient-section-tensor-transport-normalized-pure).

Proof: the local map sends a scalar tensor of a pure tensor to the tensor of the
unit scalar with the first factor and the original scalar with the second factor.
Balancing and restriction compatibility descend this formula through sheafification. -/
theorem section_tensor_transport_normalized_pure (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T) :
    ∃ e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
        (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
          (curriedTensor (modules Λ' T)),
      ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W) (n : N.val.obj W)
        (s : (ring Λ' T).obj.obj W),
        (((e.app M).app N).val.app W)
            (sectionScalarElement a T c (M ⊗ N) W
              (sectionPureTensor Λ T M N W m n) s) =
          sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
            (sectionScalarElement a T c M W m 1)
            (sectionScalarElement a T c N W n s) := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
