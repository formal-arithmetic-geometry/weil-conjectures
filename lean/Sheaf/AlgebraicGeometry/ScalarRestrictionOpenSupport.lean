/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction

/-! # Scalar restriction preserves ordinary open support

Source: Stacks Project, Modules on Sites, Tag 03DI, the sheafified direct-sum
construction of extension by zero (blueprint: lem-sf-scalar-restriction-open-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

/-- Restricting a single constant coefficient action preserves open support.

Source: Stacks Project, sites-modules.tex, Tag 03DI (lemma-extension-by-zero),
using Tag 03CY (lemma-sheafification-presheaf-modules)
(blueprint: lem-sf-scalar-restriction-open-support).

Proof: identify the small pro-etale site of U with the site localized at the
subterminal open j. The specified module pullback is restriction in these coordinates;
adjoint uniqueness identifies its chosen left adjoint with localized extension by zero.
For a localized A-module M, the extension presheaf at H is the direct sum of M(H -> U)
over lifts H -> U. Restrict the action on each summand through a. The two resulting
presheaves have the same underlying additive groups, restrictions, and B-actions.
Identity on each summand therefore identifies restriction of the A-extension
presheaf with the B-extension presheaf of the restricted localized module. The same
identity extends to sheafification: restriction changes only the action, and the
underlying additive sheafification is unchanged. Thus the restricted extension lies
in the essential image of the chosen B-extension. Its B-open counit is invertible,
since open extension is fully faithful. The argument includes the empty open, where
both extension presheaves are zero, and the identity open, where restriction is the
identity. It assumes no flatness of a. -/
theorem restrictScalars_openCounit_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {U X : Scheme.{u}} (a : coefficients B X ⟶ coefficients A X)
    (j : U ⟶ X) [IsOpenImmersion j] (M : Modules A U) :
    IsIso ((moduleJAdj.{u} B j).counit.app
      ((Scheme.proEtaleRingRestrictScalars a).obj
        ((moduleJ.{u} A j).obj M))) := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower
