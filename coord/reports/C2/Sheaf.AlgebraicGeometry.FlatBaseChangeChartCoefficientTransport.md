## What changed

Completed the unchanged theorem exists_flatBaseChange_chart_coefficient_transport
from one strictly smaller invertibility statement in the new module
Sheaf.AlgebraicGeometry.FlatBaseChangeChartUnitIso. The geometric chart and both
projection equations are proved using Mathlib's restricted pullback square and
affine chart isomorphisms. The coefficient map is constructed explicitly by the
inverse adjunction hom-equivalence. Its unit equation is proved by the adjunction
law. A private proved helper constructs the reciprocal coefficient map from its
inverse and proves both composite identities; multiplication naturality proves
the scalar square. The sole new import is a proof-only import. The original
signature and public imports are unchanged. No definitions or other modules
were changed, and no witness was selected to define any object.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.Scheme.Modules.exists_flatBaseChange_chart_coefficient_transport
(node new-flat-base-change-chart-coefficient-transport). Its entire combining
proof compiles without sorry.

Added one hole:
AlgebraicGeometry.Scheme.Modules.isIso_flatBaseChange_chart_unit_adjoint
(node new-flat-base-change-chart-unit-iso). It asserts only invertibility of a
specified adjoint map on an already given geometric chart. It does not construct
the chart, assert scalar compatibility, provide a reciprocal map or assert the
unit equation. Those parts are proved in the original module. This is a
one-hole-to-one-hole decomposition, with net hole count zero, not a claim of an
axiom-free proof of the full coefficient theorem.

The private chart_geometry and exists_pushforward_iso_coefficient_inverse
helpers are proved without sorry. No other holes are left or added.

## No longer needed

No original Lean import was removed: both public imports are required by the
unchanged statement. The planned dependency def-pc-tensor-pullback-composition-iso
and its module Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso are not used
by this reduction or the new lemma's proof plan. Ordinary Mathlib pullbackComp
and uniqueness of left adjoints suffice. This removes that dependency from this
node, without claiming it is globally unreachable from other targets.
All other original proof dependencies remain needed, either in the combining
proof or in the new invertibility lemma.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool failure found. The original second proof step bundled
coefficient invertibility, reciprocal identities, scalar compatibility and unit
compatibility. Only invertibility needs to remain open: defining phi as an
explicit adjoint makes the unit square formal, and the other identities follow
from geometric projections and inversion. The original geometry plan can be
implemented more directly with Scheme.Hom.isPullback_resLE and IsPullback.of_iso.
The unit record sk-thm-p1 and all of its realized statement/step nodes are unchanged.

## New nodes

new-flat-base-change-chart-unit-iso records exactly the IsIso assertion for the
explicit adjoint of b on any given chart over the original scheme. Its statement
drops affine hypotheses and algebra-map compatibility because ef already gives
the only geometric equality needed for coefficient transport. Its docstring
explains comparison of tensor and ordinary pullbacks by uniqueness of adjoints,
composition and restriction, then identification of the adjoint by D.unit_square.
Edge cases checked in the argument: empty opens/schemes, zero coefficients, and
identity charts use the same adjunction identities; no nonempty or nonzero
hypothesis is used. In particular phi is explicitly constructed, and its inverse
is chosen only after IsIso of this specified map, so uniqueness determines it.

Searches used LeanFinder, Loogle, grep and LeanSearch (the latter returned Internal
Server Error, recorded as unavailable). The library and blueprint were searched
by coefficient transport and tags 0096/0097; no exact existing statement was found.
No change record is needed because all existing interfaces are preserved.

## Second reading by C2

1. Compared the delivered coefficient-transport module with the repository version. The theorem signature and its two public imports are byte-for-byte unchanged; only the proof-only import and proof body were added. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py`; there are no errors, forbidden declarations, or unsplit `sorry`s in the item. The sole remaining `sorry` is the named theorem `isIso_flatBaseChange_chart_unit_adjoint`, with its own node and proof docstring. Verdict: pass.

3. Checked the split statement against its use: it asserts `IsIso` only for the explicitly defined adjoint map, with no extra geometric or scalar conclusion. The construction in the item is explicit, and the reciprocal map is selected only after this specified map is known invertible. Local edge cases (empty opens, zero modules, identity charts) introduce no additional hypotheses. Verdict: pass.

4. The proof follows the shortest available route through `isPullback_resLE`, affine chart isomorphisms, adjunction identities, and naturality. The former tensor-pullback composition dependency is unused and is removed from the item node's proof dependencies; no public import was unnecessarily removed. Verdict: pass.

5. The item node proof steps and dependencies now match the Lean proof, and the new split node contains the required statement, source, proof plan, searches, Lean record, chapter, and unit. The unit route and all realized unit steps remain unchanged. Verdict: pass.

Changed after this reading: added this review record only; no Lean declarations or statements were changed.
