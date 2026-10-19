/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.RingedRefinementModels
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.SixFunctors.OpenTensorNormalization

/-! Normalized ringed refinement construction and comparison obligations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory AlgebraicGeometry SheafOfModules.OpenTensorNormalization

namespace SheafOfModules.RingedRefinement

/-- Constant finite coefficients identify the ringed vertical-site refinement
with the specified strict-tower refinement. This assertion only compares the two
presentations; it asserts no coefficient-change or refinement-composition law.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement, step 11;
Stacks 00Z4, 03D1, 0H7J (blueprint: lem-pur-ringed-refinement-finite-comparison).

Proof: apply the section-preserving product-site module realization. The inverse
image of a constant ring is the same constant ring, with map adjoint to the fixed
constant-section map; this gives `constant_hom` and the scalar equation.
The ordinary direct-image comparison is identity on the resulting additive
sections. Its adjoint is the ordinary pullback comparison, and exact localization
gives the specified pull model. The derived adjunction determines the direct-image
comparison, preserving its unit and counit. The open unit similarly determines
shriekIso. Under these identifications beta is the open-unit normalized strict-tower
beta, pi is its identity/zero clopen projection, and the two open-composition maps
are adjoints of the same restriction compositor. Thus their composite is the
strict-tower alpha. Transporting proper-adjunction mates identifies the resulting
refinement with gamma. In the source its proper map is the identity of X;
the inverse canonical identity-proper comparison is precisely the extra factor
in `FiniteNormalization`. These are equations of maps under the constructed
comparisons, never consequences of levelwise detection of derived equality. -/
theorem exists_finiteRefinementComparison {T : Scheme.{u}} (P : Package .systems T)
    (B : Type (u + 1)) [CommRing B] [Finite B] :
    ∃ (e : ∀ W : Over T, FiniteRealization P B W) (k : FiniteComparison P B e),
      FiniteNormalization P B e k := by sorry

end SheafOfModules.RingedRefinement
