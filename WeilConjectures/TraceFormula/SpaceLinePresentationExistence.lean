/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.SpaceLinePresentationDefs

/-!
# Effective descent of a small-etale line module to scheme tests

Source: Stacks Project, Properties of Spaces, Tags 03G7 and 03M3;
Descent, Tags 03DX, 023T and 05VG
(blueprint: lem-trf-cartesian-line-presentation-existence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A line module has an invertible cartesian realization on all scheme tests.
This is only effectivity; it makes no assertion about morphisms or uniqueness.

Source: Stacks, Properties of Spaces, Tags 03G7 and 03M3;
Descent, Tags 03DX, 023T and 05VG
(blueprint: lem-trf-cartesian-line-presentation-existence).

Proof: restrict the given module to an etale scheme atlas. Its local rank-one frames
make it an etale line module on the atlas scheme. The Zariski/etale equivalence for
quasi-coherent modules, restricted to rank one, gives an ordinary invertible module.
The two restrictions on the scheme double overlap correspond to the same etale
module, hence full faithfulness gives the transition isomorphism; faithfulness gives
the cocycle. On each scheme test pull back this atlas and its transition functions.
The projections form an etale, hence fpqc, cover of the test scheme. Effective descent
for quasi-coherent modules gives an ordinary module, and rank-one local freeness
descends, so it is invertible. Choose these descended modules together with their
atlas identifications. Full faithfulness of descent gives the tensor-pullback
identification for each test morphism, retaining the atlas identifications. It also
gives its identity and composition equations. On a small-etale test, the original
module and the descended module have the same local frames and transitions, so the
sheaf axiom glues the additive section equivalence. These equivalences are linear
and natural because they are so on the atlas, and retain the original module L.
Empty tests and arbitrary, possibly infinite, atlas refinements are allowed. -/
theorem exists_etaleLinePresentation (X : AlgebraicSpace S) (L : X.Modules)
    (hL : X.IsLineModule L) : ∃ P : EtaleLinePresentation X, P.line = L := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
