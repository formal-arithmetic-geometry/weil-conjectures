/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.CategoryTheory.CondensedTensorInductionData
import Sheaf.CategoryTheory.EquivariantModuleSheafificationReflector

/-! # Sheafification and the identity tensor

Source: induction argument, steps 1, 4--5, below direct-image stability paragraph (3).
(blueprint: lem-sfb-condensed-tensor-sheafification).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace Profinite.CondensedAction
variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]
  (P : ProfiniteGrp.{u}) (H : ClosedSubgroup P)

/-- Ordinary module sheafification realizes the tensor presheaf internally and the
identity tensor defines an H-equivariant morphism. No adjunction is assumed.
Source: induction argument, steps 1, 4--5
(blueprint: lem-sfb-condensed-tensor-sheafification).

Proof: continuous P-valued maps form a group sheaf: a compatible family descends
along a finite coproduct covering surjection, which is quotient because its source
is compact and target Hausdorff, including the empty cover. Apply the equivariant
module sheafification reflector to B's action and ordinary section ring sheaf.
The internal-module/section-module equivalence realizes each sheafified module
with this action. Extend each B.map uniquely across the sheafification unit;
uniqueness proves identity and composition and the natural comparison. Equivariance
of the unit is the reflector's unit formula. Naturality of the ordinary unit gives
the map formula on tensors. The map m to the sheafified [1] tensor m is linear
and natural. Balancing [h] tensor m = [1] tensor hm and equivariance of the unit
make it H-equivariant. Full faithfulness of the section-module equivalence gives
identityTensor with its displayed section formula. No representative of a coset
or finite-index assumption occurs.
-/
theorem tensorInductionSheafData_exists (B : TensorInductionPresheaf R P H) :
    Nonempty (TensorInductionSheafData B) := by
  sorry

end Profinite.CondensedAction
