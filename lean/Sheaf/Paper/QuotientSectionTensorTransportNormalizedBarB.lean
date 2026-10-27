/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.QuotientSectionTensorData
import Sheaf.Paper.IntegralResidueDerivedMonoidal

/-! # Underlying quotient section tensor comparison -/

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

/-- The balanced section tensor comparison exists before its normalization equations.
Source: Stacks 03EK, 03EL, 06YS, 07A4 and 0G7D; parent proof steps 1--5.
(blueprint: lem-sfb-quotient-section-tensor-transport-normalized-barB).

Proof: construct the sectionwise balancing map on flat-term K-flat representatives,
then descend it through the section localization and the resolving-class equivalence.
The signed total and the tensor counits give a natural derived isomorphism. -/
theorem section_tensor_transport_normalized_barB_exists (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b) :
    Nonempty (tensor Λ T ⋙ c.model.T ≅
        (c.model.T.prod c.model.T) ⋙ tensor Λ' T) := by
  sorry

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
