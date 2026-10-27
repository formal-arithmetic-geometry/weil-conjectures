## What changed

Added the completely proved public theorem
`CategoryTheory.brownHypothesesFor_iff_compact_representatives` in the assigned module.
It identifies Brown's bundle with thickness, essential smallness, and compactness
of any family representing the constructible finite-Tor objects up to isomorphism.
The family needs no category structure, skeletal condition, or specific indexing
universe. The coproduct universe in the bundle is unchanged. Compactness remains
an explicit hypothesis, not an asserted arbitrary-field theorem.

The existing private finite-field assembly now applies this criterion directly to
its original small skeleton and the same finite-field compactness theorem. This
removes its duplicated objectwise isomorphism-transport argument and repeated
coefficient-case smallness reduction. The required skeletal condition of the
geometric compactness input is retained exactly.

Added a matching proved DAG node and updated the item and supported finite-field
node proofs. No existing signature, declaration visibility, definition body or
import changes. No source-library or consumer module changes.

The first edited compile reached 60 seconds. A synchronous diagnostic profile
confirmed the new theorem elaborates and identified repeated braiding comparisons
in module tensor structures. Local irreducibility of internal-Hom and point-pullback constructions prevents
unrelated expansion in these comparisons. Lean rejected an attempted local
reducibility change on the braiding wrappers; that attempt was removed. No global attribute changes, no file split and no raised limit.
Temporary profiling settings are removed from the delivery source.

Change record: `coord/changes/J9-brown-representative-compactness-criterion.md`.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.
The sole direct sorry remains `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`, with its original disputed statement and proof body.
The new representative-family criterion and the revised finite-field assembly
are complete. This is a proved reusable part of the assembly, not a proof or
holed decomposition of the unsupported arbitrary-field assertion.

A declaration-parser comparison confirms one new public theorem, no removed
original declarations, no changed original signatures, and exactly one changed
original theorem body: the private finite-field assembly. All definition bodies
and imports are identical. Every Lean line has at most 100 characters.
The final server single-file compile passed in 57.5 seconds, exit 0, with no
warnings. The delivery tool runs compilation with the declaration axiom probe
and preflight.

## No longer needed

The private finite-field assembly no longer calls
`brownHypothesesFor_iff_compact_of_admissible` or repeats compactness transport
inline. Its node now uses `lem-sfb-brown-representative-compactness-criterion`
in place of `lem-sfb-brown-admissible-compactness-criterion` for this step.
The latter declaration and node remain available and unchanged; they are not
withdrawn. No import, whole module, declaration, or original item dependency is
pruned from the targets' closure. Smallness, structural clauses, finite-field
compactness and the orthogonal-generation argument remain used transitively.
No absent or quarantined parent is treated as unused.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the remaining public theorem asserts compactness over an
arbitrary positive-characteristic field. Its supplied compactness input instead
requires the algebraic closure in a FiniteFieldDatum. Separated finite type over
an arbitrary field does not supply such a datum or finite absolute cohomological
dimension. The original infinite-transcendence-degree Kummer-symbol diagnostic
remains a natural-language objection, not a formal field-cohomology counterexample.
No unsupported compactness statement or renamed copy of the original hole is added.

The existing assembly made the formal passage from representative compactness to
Brown's bundle look tied to a small skeletal category. Only the geometric input
needs that family shape. The new exact criterion isolates the formal step while
retaining thickness and essential smallness; the unit's proof route is unchanged.

Edge checks: a representative family can have repetitions or an arbitrary index
universe. An empty family is permitted only when its covering hypothesis is
satisfied; it does not bypass any constructible object. Every representative
belongs to the closure by its actual constructible finite-Tor property. Fullness
lifts the ambient isomorphism, and compactness transports for the same fixed
coproduct structure. Zero objects and zero coefficient rings cause no exception.
No data is chosen from an unproved existence theorem in the new result.

## New nodes

`lem-sfb-brown-representative-compactness-criterion` records the new proved
equivalence. Its forward direction extracts representative compactness from the
existing objectwise criterion. Its reverse direction lifts representative
isomorphisms to the actual full localizing subcategory and uses the existing
proved compactness-transport lemma before applying that criterion. It has no sorry.

Searches: launcher LeanFinder returned derived-category/t-structure infrastructure;
LeanSearch returned topological compactness, essentially-small full subcategories
and finitely presentable objects; Loogle and Mathlib grep returned zero hits.
Direct rg over Sheaf, WeilConjectures and Mathlib found the existing objectwise
criterion and private compactness-transport helper, which are reused. The new
criterion is used immediately in the original supported finite-field proof.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
