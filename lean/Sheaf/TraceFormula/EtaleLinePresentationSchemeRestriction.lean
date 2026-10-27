/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.TraceFormula.SpaceLinePresentationDefs
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction

/-! # Zariski restriction of a cartesian line presentation

Source: Stacks Project, Tags 0D3C, 0D2Z and 01O9
(blueprint: lem-trf-etale-line-presentation-scheme-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A cartesian realization on an etale test is the Zariski restriction of its line.

Source: Stacks, Properties of Spaces, Tag 03G7, and Descent, Tags 03DX and 03FH
(blueprint: lem-trf-etale-line-presentation-scheme-restriction).

Proof: for every open V of W, let W_V be its open-subscheme test and j:W_V to W the
inclusion. Compose the inverse of tensorOpenSectionIso with the section map of
P.pullbackIso j and then P.etaleSections W_V. This identifies sections of P.module W
on V with sections of P.line at W_V. The latter are the definition of schemeRestriction.
The maps are additive and linear: the tensor-open comparison uses the ordinary
regular-function restriction and etaleSections_smul preserves the same scalars.
For V contained in V', coherence of the cartesian family identifies the two composite
pullbacks along open inclusions; the identity and composition normalization for tensor
open sections identifies their section maps with ordinary module restriction.
The equation etaleSections_naturality then says exactly that the displayed additive
linear equivalences commute with these restrictions. They therefore assemble into a
module-sheaf morphism. Their pointwise inverses are also natural, and give its inverse.
Empty opens and the empty test scheme have their unique section equivalences. -/
theorem etaleLinePresentation_schemeRestriction (X : AlgebraicSpace S)
    (P : EtaleLinePresentation X) (W : X.EtaleSite) :
    Nonempty (P.module W.obj ≅ (schemeRestriction X W).obj P.line) := by sorry

end AlgebraicGeometry.AlgebraicSpace
