/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests

/-! # Zariski restriction of modules on a representable algebraic space

Source: Stacks Project, Descent, Tags 03DX and 03FH
(blueprint: def-sfb-scheme-space-zariski-restriction).

The construction specializes the existing restriction to an étale scheme chart to the
identity chart of the representing scheme. All module sections and scalar maps are those
of the original module and the canonical regular-function comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The identity of the representing scheme, regarded as its small étale chart.
Source: Stacks Project, Descent, Tags 03DX and 03FH
(blueprint: def-sfb-scheme-space-zariski-restriction). -/
def schemeSpaceIdentityEtale {S : Scheme.{u}} (T : Over S) :
    (schemeSpace T).EtaleSite :=
  ⟨CostructuredArrow.mk (yoneda.map (𝟙 T)),
    (representable_etale_scheme_tests.2.2.2.2.2.2.2.1 _ _ (𝟙 T)).2 inferInstance⟩

/-- Restriction from the small étale modules of a representable algebraic space to
Zariski modules on its representing scheme. On an open `U`, the sections are those of
the input module at `U.toScheme → T`; restriction maps are its original module maps,
and scalars are restricted by the canonical identification of regular functions.
This is the existing chart restriction at the identity chart, with no comparison
isomorphism, arbitrary module, or quasi-coherence hypothesis chosen as data.
Source: Stacks Project, Descent, Tags 03DX and 03FH
(blueprint: def-sfb-scheme-space-zariski-restriction). -/
def schemeSpaceZariskiRestriction {S : Scheme.{u}} (T : Over S) :
    (schemeSpace T).Modules ⥤ T.left.Modules :=
  (schemeSpace T).schemeRestriction (schemeSpaceIdentityEtale T)

end AlgebraicGeometry.AlgebraicSpace
