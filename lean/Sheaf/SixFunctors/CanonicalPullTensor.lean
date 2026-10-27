/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.ClopenComparisonTensorSquareData

/-! # Existence of normalized clopen tensor data -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization
namespace SheafOfModules.ClopenComparisonTensorSquare

/-- The canonical tensor comparison for a supplied geometric pullback presentation.
Source: Stacks 03EL and 07A4.
(blueprint: lem-sf-canonical-pull-tensor).

Proof: present the module inverse image as algebraic inverse image followed by
extension of scalars. Uniqueness of the adjunction to the specified sectionwise
direct image gives its comparison with p.ordinary. Transport the canonical
ordinary tensor isomorphism along that comparison. Its pure-unit formula follows
from the adjunction unit formula and the canonical pure-tensor formula. Pullback
preserves flat terms and K-flat complexes. Apply the canonical unbounded tensor
pullback theorem to the supplied tensor models and transport along the unique
left-derived comparison to p.derived. The signed total comparison commutes with
the differential degreewise, and the theorem's representative square gives the
displayed normalization after cancelling the target representative isomorphism.
This argument applies directly to the vertical ringed site, without evaluating
systems or assuming any flatness of coefficient transitions. -/
theorem canonical_pull_tensor (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology m Y) CommRingCat.{u + 1})
    (S : Sheaf (topology m X) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).obj S)
    (p : Pullback R S (direct m f R S c)) (a : TensorModel R) (b : TensorModel S) :
    Nonempty (PullTensor m f R S c p a b) := by
  sorry

end SheafOfModules.ClopenComparisonTensorSquare
