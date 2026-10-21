/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.Paper.RingedRefinementConstruction
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.RingedProjectionRestriction
import Sheaf.SixFunctors.OpenTensorNormalization

/-!
# Normalized coefficient and geometric calculus on the actual sites

(blueprint: lem-pur-ringed-refinement-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

/-- Geometric and scalar operations, before the clopen comparisons and their laws.
Source: Stacks 03D7, 06YY, 07A6; coefficient supplement Steps 1--2 and 6
(blueprint: lem-pur-ringed-refinement-core).
Proof: construct module inverse image as the left adjoint of sectionwise direct
image with the structural map obtained from the ring inverse-image compositor.
The coefficient identification after inverse image is an isomorphism, so
inverse image is exact. Module
sheaf categories are Grothendieck and have K-injective resolutions. For an open,
transport the direct-sum extension and sheafification adjunction from the localized
site; its unit is an isomorphism and extension is exact. Take each scalar universal
pair from derived change of rings. Direct-image compositors are induced on every
section by fibre-product associativity; their conjugates fix inverse-image ones.
Restriction of scalars commutes with direct image by the identity on underlying
sections; taking left mates fixes the ordinary scalar comparison. Its K-flat
localization gives the pull comparison. The open-unit transpose gives delta,
invertible by the normalized open tensor comparison. Balanced tensor associativity
and the unit are localized on K-flat representatives to give ScalarComposition.
All constructions apply on the vertical sites with unchanged coefficient index. -/
theorem ringedRefinementCore (m : Mode) (T : Scheme.{u}) :
    ∃ (o : Calculus (canonicalCoefficients m T)) (p : Spatial o)
      (sc : ScalarComparisons o), Nonempty (ScalarComposition o) := by
  sorry

end SheafOfModules.RingedRefinement
