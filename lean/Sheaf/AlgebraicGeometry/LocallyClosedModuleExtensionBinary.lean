/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.AlgebraicGeometry.LocallyClosedModuleExtensionModel

/-!
# Objectwise normalized composition for the fixed locally closed model

Source: Stacks Project, Tags 09AH and 02V0.
(blueprint: lem-sfb-locally-closed-module-extension-binary).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Two fixed extensions have a normalized comparison on each input module.
This assertion has no naturality, identity comparisons, or associativity conclusions.

Source: Stacks Project, Tags 09AH and 02V0; Steps 3--8 of
lem-sfb-locally-closed-module-extension-coherence.
(blueprint: lem-sfb-locally-closed-module-extension-binary).

Proof: write a = v c and b = w d using their chosen factorizations. Lift the open w
in the closed subscheme c to an ambient open h; its intersection with c is a closed
e with c w = h e. The localization sequence and the two complementary vanishing
restrictions identify c_* w_! M with h_! e_* M. The actual identified-coefficient
supported-reconstruction theorem constructs the isomorphism and proves its restriction
equation using the open unit and closed counit. The open-restriction-counit theorem
matches that equation with the restriction of c_* w_!. Compose the pure open factors
by uniqueness of left adjoints with their specified units. Compose the pure closed
factors by fibre-product pasting of direct images; its conjugate inverse-image map is
the specified pullComp. The resulting functor is the closed-then-open extension for
(v h)(e d). Intersect its ambient open with the one chosen for ab and shrink both as
in the boundary comparison. Each map preserves restriction, so their composite has
the displayed normalization. For uniqueness, conjugate the source by one such
isomorphism. Full faithfulness of the model for ab, together with modelRestriction,
makes its pullback injective on morphisms between its image objects. The displayed
equation fixes the pullback, hence the hom and the entire isomorphism. These arguments
apply to zero modules and empty or identity factors without change. -/
theorem locallyClosedModel_binary_exists {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (M : proEtaleRingModules T.scheme T.ring) :
    ∃ e : a.modelExtension.obj (b.modelExtension.obj M) ≅ (a.comp b).modelExtension.obj M,
      LocallyClosedObjectNormalization (a.comp b).modelExtension (a.comp b).pull
        (a.comp b).modelRestriction
        (LocallyClosedCompositeRestrictionMap a.modelExtension b.modelExtension a.pull b.pull
          (a.comp b).pull a.modelRestriction b.modelRestriction (a.pullComp b) M) e := by
  sorry

/-- A family of normalized natural binary comparisons for the fixed model.
It is a parameter of the formal unit/associativity assertion, not an existence claim.
Source: Stacks, Tag 02V0
(blueprint: lem-sfb-locally-closed-module-extension-binary). -/
structure LocallyClosedModelComposition where
  gamma : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    b.modelExtension ⋙ a.modelExtension ≅ (a.comp b).modelExtension
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    LocallyClosedBinaryNormalization a.modelExtension b.modelExtension a.pull b.pull
      (a.comp b).pull (a.comp b).modelExtension a.modelRestriction b.modelRestriction
      (a.comp b).modelRestriction (a.pullComp b) (gamma a b)


end AlgebraicGeometry.Scheme
