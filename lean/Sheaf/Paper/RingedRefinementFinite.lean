/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.Paper.RingedRefinementConstruction
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus

/-!
# Finite constant coefficients and the intrinsic strict tower realization

(blueprint: lem-pur-ringed-refinement-finite-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

/-- Section-preserving realization identifies the finite refinement with strict towers.
Source: coefficient supplement Step 10; Stacks 00Z4, 03D1, 0H7J, 07A6
(blueprint: lem-pur-ringed-refinement-finite-normalization).
Proof: the section-preserving diagram-site equivalence identifies strict constant
coefficient towers with module sheaves over the vertical constant ring. Inverse
image preserves that ring and its constant sections, so transport along the canonical
constant-ring isomorphism gives each FiniteRealization, with the stated scalar action.
Direct image is precomposition on sections, giving ordinaryPush. Conjugating this
comparison by the fixed ordinary adjunctions gives ordinaryPull and its unit formula.
Localizing fixes pull and its cochain equation. The derived adjunction comparison
then fixes push and its unit/counit equations. The open unit fixes shriekIso. The three
normalized h factors become the strict-tower alpha: both are the open-unit base change,
the clopen projection, and open composition. Apply the proper-adjunction Hom bijection
to identify their refinement mates, inserting the identity proper comparison. This is
exactly FiniteNormalization and uses no detection of derived morphisms by evaluation. -/
theorem ringedRefinementFinite {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] [Finite B] :
    ∃ (e : ∀ W : Over T, FiniteRealization P B W) (k : FiniteComparison P B e),
      FiniteNormalization P B e k := by
  sorry

end SheafOfModules.RingedRefinement
