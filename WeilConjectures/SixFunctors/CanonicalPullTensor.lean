/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ClopenComparisonTensorSquareData
public import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.OpenOperationModels

/-!
# Canonical tensor comparison for a supplied pullback

Source: Stacks Project, sites-cohomology.tex, Tags 07A4
(lemma-pullback-tensor-product) and 0G7E (lemma-pullback-K-flat), together with
sites-modules.tex, Tag 03EL (lemma-tensor-product-pullback)
(blueprint: lem-sf-canonical-pull-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.ProjectionRestriction
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.ClopenComparisonTensorSquare

/-- The supplied ordinary adjoint and its universal left derived functor admit
canonical tensor comparisons, normalized on pure tensors and signed total complexes.
Both the ordinary pro-etale site and the vertical inverse-system site are covered.
Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0G7E, and
sites-modules.tex, Tag 03EL (blueprint: lem-sf-canonical-pull-tensor).

Proof plan:
1. Present module inverse image as algebraic inverse image followed by extension
   of scalars. Uniqueness of the adjunction to the specified sectionwise direct image
   identifies this construction with `p.ordinary` (lem-sf-open-operation-models).
2. Transport the canonical ordinary tensor isomorphism along that identification.
   The adjunction unit formula and the pure-tensor formula give `pure_unit`.
3. Pullback preserves flat terms and K-flat complexes. Apply the canonical
   unbounded tensor-pullback theorem to the supplied tensor models and transport
   along the unique left-derived comparison to `p.derived`
   (lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
4. The signed total comparison commutes with the differential degreewise. The
   representative square, after cancelling the target representative isomorphism,
   is precisely `PullTensor.representative`.
5. Apply the same construction directly to the vertical ringed site for systems;
   no evaluation of systems or flatness of coefficient transitions is required. -/
theorem canonical_pull_tensor (m : Mode) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology m Y) CommRingCat.{u + 1})
    (S : Sheaf (topology m X) CommRingCat.{u + 1})
    (c : R ⟶ ((baseChange m f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology m Y) (topology m X)).obj S)
    (p : Pullback R S (direct m f R S c)) (a : TensorModel R) (b : TensorModel S) :
    Nonempty (PullTensor m f R S c p a b) := by
  sorry

end SheafOfModules.ClopenComparisonTensorSquare
