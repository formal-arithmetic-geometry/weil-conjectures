/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.Paper.CompositionModelOrientationDefinitions

import Sheaf.Paper.AffineOrderedIntegrationTransposes
import Sheaf.Paper.AffineCoefficientCounitNormalization
import Sheaf.Paper.VectorBundlePurity
import Sheaf.Paper.VectorIntegrationSiteComparison
import Sheaf.Paper.CompactSupportSiteCoherence

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The ordered integration comparisons give normalized affine orientations, their
zero-section multiplication, and the three normal-coordinate beta identifications.
Source: thm-pur-composition-coherence.proof.md, Step 1, expanded in model descent
Steps 2--5 (blueprint: lem-pur-model-affine-integration-orientation).

Proof: identify the ordered affine comparison at every positive coefficient level
with the integration transpose. Its inverse is the normalized vector-bundle orientation
by projection purity agreement. Transport through the prescribed ordered coordinate
isomorphism to obtain G; no arbitrary affine frame is selected. The identity adjunction
at rank zero gives the unit equation. Apply integration-normalized direct-sum purity
to the two coordinate bundles and transport its projection and compositor through
the proper/open site comparisons. Coefficient-counit normalization rewrites its
coefficient-dependent transpose as theta applied to the unit transpose. Naturality
and cancellation of these invertible transposes give the affine equation. Pull back
along the total zero section; the prescribed base-change maps identify its two factors
with b_d and b_e, proving zero-section multiplication. The normal-bundle frames of the
compatible DNC charts identify their integration-normalized beta maps with these b_r.
The same unit and empty-frame formulas handle zero rank and empty bases. -/
theorem model_affine_integration_orientation (P : PurityFiniteSetting.{u}) (d e : ℕ) :
    ∃ G : P.ModelAffineGamma,
      P.ModelGammaNormalization G ∧ P.ModelGammaZeroNormalization ∧
      (∀ (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
        [LocallyOfFiniteType aB] [QuasiCompact aB],
        ModelAffineOrientationEquation P G B d e aB ∧
          ModelZeroOrientationEquation P G B d e aB) ∧
      ∀ (U V T : Scheme.{u}) [IsAffine U] [IsAffine V] [IsAffine T]
        (f : U ⟶ V) (g : V ⟶ T)
        [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
        [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
        (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT],
          ModelChartBetaIdentification P G d e f g aT := by sorry

end WeilConjectures.PurityFiniteSetting
