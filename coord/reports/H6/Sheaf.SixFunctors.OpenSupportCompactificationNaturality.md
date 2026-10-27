## What changed

Preserved the signature and public imports of
AlgebraicGeometry.Etale.openSupportCompactificationIso_naturality.
The proof uses the existing graph normalization and cocycle API to identify
composition with a specified cartesian refinement. It factors the support
comparison into its graph map and literal-pullback comparison, proves refinement
compatibility, and uses the two projections of the actual common refinement to
obtain the required naturality square.

OpenSupportPullbackModel constructs openSupportPullbackIso from the existing
proper/open exchange and open-extension compositors. It adds no choices or
postponed data. OpenSupportRefinementExchange proves compatibility with one
supplied cartesian refinement and its literal pullback.

For that theorem, construct the triangles (p,j) and (a,f), both with output
c.precomp a. Apply the existing compIso_naturality to their refinement morphisms.
Remove the trivial proper identity factors, identify the exact open compositor
and proper/open exchange, and cancel their common normalized (a,f) compositor.
A private generic raw comparison packages the exchange/compositor construction;
its factorization is checked abstractly before specializing to derived functors.
This avoids repeatedly unfolding large derived-category constructions.

The private arbitrary-scheme unboundedFormalism implementation and its proved
exchange, compositor and refinement identifications are imported as proof tools.
Their statements have no Noetherian or open-quasi-compactness assumptions.
Some public theorems in that module do; those theorems are not applied.
All added imports in the original item are private proof imports. No existing
source-library module, target, statement, definition or public attribute was
changed. Local irreducibility attributes keep large constructions behind their
proved equations; respectTransparency is never disabled. No consumer adaptation
is required.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Etale.openSupportCompactificationIso_naturality
(node lem-asd-open-support-compactification-naturality).
The new theorem AlgebraicGeometry.Etale.openSupportPullbackIso_refinement
(node lem-asd-open-support-refinement-exchange) is also proved.
All private helpers are proved. The three delivered Lean modules contain zero
sorry tokens: one original hole closed, zero holes added, zero split off.
Existing recorded graph-normalization dependencies are used as declarations;
no duplicate hole for them is introduced.

All three modules compiled through lcompile.py with profiling removed:
OpenSupportPullbackModel in 30.8 seconds, OpenSupportRefinementExchange in
40.2 seconds, and the final OpenSupportCompactificationNaturality in 7.2 seconds.
Every file is below the 60-second limit.

The identity-refinement, empty-scheme, empty-open and zero-ring cases use the same
unit/compositor equations. Only isomorphisms are cancelled. No density or
quasi-compactness assumption on either open is introduced.

## No longer needed

No original import was removed and no whole module is pruned.
The item's old direct proof dependencies
lem-etale-unbounded-compact-support-composition,
lem-kun-proper-base-change-torsion-ring,
lem-cbc-extension-zero-base-change,
lem-cbc-extension-zero-composition, and lem-weil-pbc-mate-pasting
are replaced in its node by the graph API and refinement equation.
Their constructions remain needed transitively. There is no request to withdraw
these nodes or any adopted source-library declaration.

Repeating the product-graph normalization here is unnecessary: the existing
graph API supplies it. A further unfinished unit/mate-pasting lemma is also
unnecessary: the proved generic triangle-naturality calculation supplies the
coherence after the two explicit specializations.

## Where the brief, the DAG or earlier work was wrong

The old proof plan did not identify the available graph/common-refinement
normalization or the triangle-composition naturality API. Both can be reused.
The general compact-support comparison module initially looks unsuitable because
its public statements often assume Noetherian schemes. Its private formalism,
proper/open exchange, exact open compositor and refinement-comparison lemmas
are proved for arbitrary schemes. Using these implementation lemmas closes the
single-refinement equation without strengthening its hypotheses.
This follows the unit's compactification route. No blueprint-unit statement or
realized proof step is bypassed. No source-library boundary exception is needed.

## New nodes

def-asd-open-support-pullback-model records the graph-free comparison constructed
from the existing proper/open exchange and open-extension compositors.

lem-asd-open-support-refinement-exchange records the proved single-refinement
theorem and two-triangle argument, with its existing formalism dependency.

Both inherit the item's chapter and unit. LeanSearch, Lean Finder, Loogle,
Mathlib grep and repository searches found generic mate-pasting operations;
local searches then found the graph normalization and composition API used here.
No change record is required because no existing interface changed.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
