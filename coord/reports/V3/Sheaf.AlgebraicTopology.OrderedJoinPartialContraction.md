## What changed

Proved `AlgebraicTopology.OrderedJoin.partialContraction` from the existing
`singleColorIdentities` and `functorialExpansion` declarations. Proved the
prefix recursion, differential commutation, telescope, support vanishing,
naturality of the prefix and contraction, and concatenation of the individual
subset expansions as private helpers. The theorem's statement is unchanged.

Extracted all existing chain constructions verbatim into
`Sheaf.AlgebraicTopology.OrderedJoinChains` and publicly reexported them from
the item. The prerequisites now publicly import the data module, which permits
the item to privately import their theorems without an import cycle. No data,
name, type, universe, visibility, coefficient formula or degree convention
changed. New definition node `def-sfb-ordered-join-chains` owns these constructions.
Change record: `coord/changes/ordered-join-chains-extraction.md`.

## Proved and sorry left

Closed one original hole: `AlgebraicTopology.OrderedJoin.partialContraction`
(node `lem-sfb-ordered-join-partial-contraction`). Zero holes remain in the item.
Zero holes added; zero results split off. All private helpers are proved.
The four changed modules compile cleanly via lcompile.py --all: constructions
0.0 s, functorial expansion 3.5 s, single-color identities 4.5 s, and item 5.0 s.
Both unchanged downstream consumers compile against the overlay: coset comparison
2.2 s and finite-index rectangle primitive operator 3.1 s. Their temporary
unchanged sandbox copies are excluded from the packet.

Both adapted prerequisites now retain their complete, recently landed proofs:
`AlgebraicTopology.OrderedJoin.singleColorIdentities` and
`AlgebraicTopology.OrderedJoin.functorialExpansion`. No delivered module contains
a hole; the construction module has no holes.

## No longer needed

The proof does not import or use
`Sheaf.AlgebraicTopology.OrderedJoinPrefixTelescope` or its node
`lem-sfb-ordered-join-prefix-telescope`. Its concrete linear-map telescope and
support-vanishing calculation are proved directly. This avoids constructing
a bundled chain complex and transporting components along integer equalities.
No blueprint unit route is bypassed: the unit has no realized entry for this
abstract supporting lemma, and the parent keeps the same mathematical steps.
No module is withdrawn, and other parents may still use the abstract lemma.

The original public Mathlib imports are now in the constructions module and
remain available by public reexport. Both actual prerequisite imports are
private proof imports. No unused proof import remains.

## Where the brief, the DAG or earlier work was wrong

The prerequisite single-color and functorial-expansion modules imported the
parent for its definitions. Thus the suggested parent assembly from those
statements had an import cycle. The earlier node review already noted that
the constructions needed their own definition module. This delivery performs
that extraction, leaving every definition body identical. The new definition
is tested by comparison of the original and extracted source blocks.

The abstract prefix theorem is mathematically adequate but requires substantial
chain-complex packaging and transport glue. The direct linear-map argument
proves precisely the same calculation, with no additional statement assumptions.
The full theorem retains all integer degrees, arbitrary vertex maps, and the
uncollected, color-dependent subset recipe. Empty degree -2 is handled by
nonexistence of symbols; the support argument only uses q≤r-2 and therefore
also covers all excluded lower degrees.

## Forced adaptations

With both prerequisite files restored to their original line-8 imports,
`lcompile.py --all` rejects the packet before Lean runs:
"the modules import one another in a cycle:
Sheaf.AlgebraicTopology.OrderedJoinFunctorialExpansion,
Sheaf.AlgebraicTopology.OrderedJoinPartialContraction,
Sheaf.AlgebraicTopology.OrderedJoinSingleColorIdentities".
Only line 8 changes in each prerequisite module, from public import of the item to
public import of OrderedJoinChains. The prerequisites were previously held by G7 and G9; both claims have
closed after their proofs landed. They are currently unclaimed. The adapted set compiles
in import order. No existing declaration signature or visibility changes.
The two corresponding nodes gain the construction dependency in their proof
records, and their Lean notes name its new location. Statements stay unchanged.

## New nodes

`def-sfb-ordered-join-chains` records the already-existing ordered colored-face
chain constructions in their new module. It adds no new mathematical object,
no theorem and no hole. Sources and the inherited blueprint route are retained;
four actual Mathlib searches are recorded. Search results for free abelian
groups and alternating simplicial complexes have different indexing data;
Finsupp.linearCombination is used for the existing concrete construction.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
