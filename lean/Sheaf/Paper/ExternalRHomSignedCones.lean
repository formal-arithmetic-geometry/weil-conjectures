/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J7
-/
module

public import Sheaf.Paper.ExternalRHomConePairingDefs
import Sheaf.Paper.GlobalHomEvaluationFlatLift
import Sheaf.Paper.LiftedExternalEvaluationChainModel
import Sheaf.Paper.ExternalEvaluationTransposeNatural
import Sheaf.Algebra.Homology.ExternalEvaluationTwoShiftSquares

/-! # Signed shifts and coefficient cones -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated.Opposite
namespace AlgebraicGeometry.Etale.ExternalRHom
variable (A : Type (u + 1)) [CommRing A]
attribute [local instance] derivedBraiding siteDerivedMonoidal
  siteDerivedClosed siteLocalizationMonoidal constantComplexOplax pullComplexMonoidal
  complexesBraiding coefficientComplexMonoidal

/-- The native external evaluation respects both coefficient cones for the fixed
normalized Hom shift. This is the transport from chain models to the native image
triangles, including their prescribed connecting component.

Source: Stacks 08JC and 0A90; external RHom assembly steps 3--5
(blueprint: lem-pur-external-rhom-signed-cones).

Proof: Fix bounded-below targets K,L and their external tensor F. The given S is
natural in target maps, so comparison with K-injective representatives transports
its normalization to K,L,F. Use globalHom_evaluation_flat_lift for bounded flat
representatives of the coefficient objects. Use the common shifted lifts of
lifted_external_evaluation_shifted_lift and normalize their localizations by
lifted_external_evaluation_chain_model. Apply external_evaluation_two_shift_squares
on P after the constant-ring realization. Its E equation has sign sq+s and its H
equation has sign sq+q+r. Transport through the normalized Hom models and cancel
the source and target model isomorphisms. This gives shift compatibility of the
native pairing for S, with tensorRight unsigned and tensorLeft signed.

Hom into a K-injective carries the opposite cone triangle to its Hom cone
triangle, with precisely the signed Hom shift. Derived sections, exact inverse
image and each derived tensor functor preserve distinguished triangles. Thus the
two displayed native composites carry each coefficient triangle to distinguished
triangles with the comparisons fixed by S. Four-variable naturality supplies
the first two squares. At the connecting arrow d, naturality says
B(d) lambda_at_shift = lambda A(d). Substitute the appropriate shift equation
and shift this equality once; this is exactly the third triangle square,
including the common opposite-triangle rotation sign. The triangle morphism has
all three components equal to the specified pairing, in either coefficient.
All choices here are proof witnesses, not definitions of the canonical maps. -/
theorem external_rhom_coefficient_cones
    (S : ∀ (X : Scheme.{u}) (K : DerivedCategoryModule A X),
      (homFirst A X K).CommShift ℤ)
    (hs : HasSignedHomShift (homShift := S) A) :
    PreservesCoefficientCones (homShift := S) A := by sorry

end AlgebraicGeometry.Etale.ExternalRHom
