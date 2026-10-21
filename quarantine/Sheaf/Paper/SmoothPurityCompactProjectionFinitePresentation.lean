/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.SmoothPurityCompactProjectionData
import Sheaf.Paper.RingedProjectionRestriction
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Normalized compact-projection presentations

Source: Stacks 03D7, 07A4, 03DI, 0GL1 and the finite/tower construction in
blueprint `lem-sp-compact-projection-base-change`, proof step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace AlgebraicGeometry.ProEtale.CompactProjectionBaseChange

/-- Simultaneous canonical module operations and normalized open comparisons for a
constant finite ring. The operations are fixed by their displayed section maps,
module adjunctions, exact localization, and pure-tensor/K-flat normalizations.
Source: Stacks 0H7J, 03D7, 03DI, 07A4 and 0GL1
(blueprint: lem-sp-compact-projection-finite-presentation).

Proof: take the actual constant ring sheaves and constant-section structural maps.
The constant-ring inverse-image identification identifies module pullback with exact
inverse image of A-module sheaves. Its sectionwise right adjoint and K-injective
resolutions give `Operation`. Construct the same derived tensor at every scheme by
localizing signed total tensor on flat-term K-flat complexes. Pure scalar-extension
tensors give `OrdinaryTensor`, and totalization and descent give `TensorComparison`.
Use exact extension by zero as the module left adjoint to open restriction; its unit
is invertible on sections. For every commutative square the fibre-product comparison
induces the direct-image isomorphism on sections, with precisely `rightSections`.
The open normalization theorem identifies the adjunction projection and open-square
mates with the invertible open tensor and base-change comparisons. Thus the
constructed presentation has `OpenComparisons`. All choices are of adjoints or
localized functors with their stated universal properties and normalizations. -/
theorem finite_presentation_exists (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ o : Presentation (finiteCoefficients A), Nonempty (OpenComparisons o) := by
  sorry

end AlgebraicGeometry.ProEtale.CompactProjectionBaseChange
