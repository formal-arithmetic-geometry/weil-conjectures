## What changed

Added two completely proved public declarations in the item module:
`CategoryTheory.brownHypothesesFor_iff_compact_of_noetherian` and
`CategoryTheory.brownHypotheses_of_finiteFieldDatum`.

The first generalizes the existing finite-type compactness equivalence to every
compact locally Noetherian scheme. It uses the actual six-case admissibility
predicate. The original finite-type criterion now follows by specializing this
new theorem, with its signature unchanged. The second exposes the supported
geometric finite-field Brown assembly through the actual admissibility predicate
and an explicit structure morphism. It does not replace an arbitrary field with a
finite-field datum. All six cases are permuted explicitly; no new coefficient
notion, identification, or arbitrary choice from an unproved existence is used.

Updated the existing criterion and item node proofs and added matching proved nodes.
All original signatures, definition bodies, public/private visibility and imports
are preserved. Added public import `Sheaf.Paper.FiniteFieldFiber` because the new
public signature mentions its `FiniteFieldDatum`. No source-library file or
consumer module is edited.

A local instance priority selects the existing direct pro-etale sheaf braiding.
Profiling showed elaboration comparing the direct braiding with the symmetric
localization construction repeatedly. The priority avoids that expensive reduction;
no instance definition or public attribute changes.

Change record: `coord/changes/W4-brown-noetherian-and-finite-field-api.md`.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.
The sole remaining sorry is `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`, with its original disputed statement and body.
The two new theorems and the revised proof of the finite-type criterion are complete.
This packet is a proved generalization of the criterion and a public supported
specialization, not a proof or decomposition of the arbitrary-field hole.

A source-parser comparison confirms every original declaration signature, kind,
and visibility is identical, and the direct sorry inventory remains exactly the
single original declaration. All Lean lines satisfy the 100-character limit.
The first edited-version compile reached the fixed 60-second timeout. Profiling
identified expensive braiding comparisons, repaired by the local instance priority.
The next diagnostic compile completed in 49.9 seconds and identified a missing
public import in the added finite-field signature; that import is now explicit.
Temporary profiling commands were removed. An intermediate compile exposed that
synthesizing the scheme-over morphism properties requires explicit instances.
The final proof uses a term-level `letI` for the structure morphism and supplies
its separatedness, finite-type and quasi-compactness instances from the hypotheses.
The module is not split and no limit is raised. The final server compilation
completed successfully in 55.9 seconds with no warnings. The delivery runs the
axiom probe and complete preflight before pushing.

## No longer needed

No imports, declarations, nodes or modules are pruned. The finite-type criterion's
direct coefficient-case argument is replaced by the Noetherian criterion; its DAG
proof dependency now reflects this. Smallness, structural, finite-field compactness,
and formal generation remain needed transitively. The public arbitrary-field
parents and their dependency edges remain untouched.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the remaining public theorem claims compactness over every
positive-characteristic field. The standing setting explicitly imposes no further
field hypothesis, whereas the supplied compactness theorem requires the algebraic
closure in a FiniteFieldDatum. Neither separated finite type nor coefficient
admissibility produces that datum or a finite absolute cohomological bound.
The previously recorded infinite-transcendence-degree Kummer-symbol diagnostic
remains a mathematical reason for the dispute; this delivery does not claim a
formal field-cohomology counterexample. A new arbitrary-field compactness sorry
would merely move an unsupported assertion, so none is introduced.

The human corrected the coefficient predicate to six cases on 2026-10-25. The new
API uses that actual predicate, rather than inventing another one. Its order is
finite, Z_l, Q_l, E, O_E, finite-subextension Qbar_l; the older explicit compactness
interface orders O_E before Q_l and E. The proofs account for that permutation.

Edge checks: the Noetherian criterion allows schemes not of finite type over any
field, nonseparated schemes and zero coefficients. It makes no compactness claim
from these hypotheses. The finite-field theorem covers the empty scheme and finite
rings with nilpotents, and keeps all scheme morphism assumptions of the supported
assembly. Every coproduct uses the original fixed indexing universe and every
triangulation uses the original inherited shift. No definition in a target changes.

## New nodes

`lem-sfb-brown-noetherian-compactness-criterion` records the proved equivalence on
Noetherian schemes using the existing smallness theorem and formal criterion.
`lem-sfb-brown-finite-field-admissible` records the proved geometric finite-field
specialization using the existing private assembly and its compactness dependencies.
Neither has a sorry. Both follow the original unit's thickness, smallness,
compactness and orthogonal-generation steps; no unit route is bypassed.

Searches: LeanSearch returned scheme representability, constructible subsets, the
Noetherian equivalence, HasExt and condensed infrastructure without a match.
LeanFinder returned eight sheaf-generator/condensed/geometry infrastructure
hits without the requested Brown theorem; Loogle for IsCompactObject and launcher
grep for the Brown names returned zero hits. Direct rg read the actual project
signatures and found the existing private assembly and formal criteria. Blueprint
Brown search found the original unit and detail nodes, and Noetherian compactness
found no matching blueprint node. These searches are recorded in the new nodes.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
