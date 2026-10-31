/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.SpaceLinePresentationDefs

/-!
# Fullness of cartesian line-module realization

Source: Stacks Project, Descent, Tag 023T; Properties of Spaces, Tag 03G7
(blueprint: lem-trf-cartesian-line-presentation-hom-existence).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Every map of the specified small-etale modules lifts to a cartesian
family of ordinary module maps. The map need not be invertible or nonzero.

Source: Stacks, Descent, Tag 023T, full faithfulness of fpqc descent; Properties of
Spaces, Tag 03G7 (blueprint: lem-trf-cartesian-line-presentation-hom-existence).

Proof: first work on a small-etale scheme chart. Restrict its small-etale site to
open subschemes. The given linear map, conjugated by the two section equivalences,
is a morphism of the ordinary modules there. The Zariski/etale comparison is fully
faithful, so its pullbacks agree with that same map on every further etale chart.
For an arbitrary scheme test, pull back an etale scheme atlas of the space. The two
cartesian families identify the restricted modules with tensor pullbacks of those
on the atlas. Pull back the already constructed chart maps. On double overlaps
the maps agree by naturality of the original module map and the section
identifications. Fully faithful fpqc descent of quasi-coherent module morphisms
glues them uniquely to a module map on the test scheme. Invertible modules are
quasi-coherent, so the descent theorem applies. The two composites in the cartesian
naturality equation agree after the same etale cover, hence agree by faithfulness.
On small-etale tests the construction induces exactly the specified section map.
Any other lift agrees there; after the pulled-back atlas it agrees on every scheme
test and therefore agrees globally by faithful descent. On an empty test there is
only one module morphism, and the same argument applies to empty covers. -/
theorem exists_testLineHom {X : AlgebraicSpace S} (P Q : EtaleLinePresentation X)
    (f : P.line ⟶ Q.line) :
    ∃ e : TestLineHom P.toTestLineFamily Q.toTestLineFamily,
      e.IsEtaleCompatible P Q f := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
