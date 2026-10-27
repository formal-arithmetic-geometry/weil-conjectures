## What changed

Replaced the single unfinished proof of
`WeilConjectures.PurityWeil.weilEquivarianceOfPurityAndTrace` by a complete
assembly proof, keeping its signature unchanged. A proved private categorical
lemma derives the three squares from purity naturality, a counit mate equation,
counit naturality and support-exchange naturality. The third square is actually
pasted from the first two; it is not left as a new assumption.

The finite clause applies the existing finite geometric purity mate. Its
naturality is transported from intrinsic smooth purity through the equivalence
units. Support-exchange naturality is proved by composing the actual
proper/open and pullback naturality squares, and counit naturality uses the
existing exceptional counit theorem. The rational and common clauses apply
`rational_weil_purity_naturality_mate`, followed by the same categorical argument.
The integral clause applies the two new intermediate statements listed below.

Moved all thirteen existing equivariance definitions, without changing their
signatures or bodies, to `Sheaf.Paper.WeilPurityEquivarianceData`. The item
publicly reexports that module, which preserves every former public import.
This permits the new integral lemmas to use the specified maps without a cycle.
A source comparison ignoring comments verified that the entire definition block
is unchanged. No other existing Lean module is changed. The downstream tool
found zero current importers of the item.

The item privately imports finite mate, smooth purity naturality, rational
naturality/mate and the two new integral lemmas. Local reducibility annotations
allow the proof to see the existing coefficient, fixed-pullback and compact-support wrappers;
they change no exported definition or attribute.

Mathlib searches were actually run through the launcher: LeanFinder, Loogle,
grep and LeanSearch. They found categorical counit naturality, used here, but
no theorem identifying the completed geometric purity and support comparisons.
The new nodes record the exact queries and results. Existing library searches
found the finite mate and rational/common naturality-mate theorem used here.

Validation: the data module and both new integral statement modules passed the
remote all-files compile. After the finite naturality fixes, the main module
compiled cleanly in 15.1 seconds, with no warnings. Its signature and the
relocated definition bodies were compared with the original sources. No current
existing downstream importer required adaptation.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityWeil.weilEquivarianceOfPurityAndTrace`
(node `thm-pur-weil-equivariance-of-purity-and-trace`). The item now has zero holes.
The finite, rational and common clauses are proved from existing declarations.
The generic three-square assembly and all finite naturality glue are proved.

Added exactly two named theorem holes, each in its own new module:

- `WeilConjectures.PurityWeil.integralEquivariance_naturality`
  (`lem-pur-integral-equivariance-naturality`): naturality of the specified
  completed purity and support exchange, for arbitrary integral arrows.
- `WeilConjectures.PurityWeil.integralEquivariance_mate`
  (`lem-pur-integral-equivariance-mate`): the inverse-purity composite satisfies
  the counit equation before selecting a strict Weil datum.

Thus one hole is closed and two are added: this is a decomposition, not a net
proof completion. Neither new lemma asserts any of the three squares or involves
phi; the main proof combines independent equations, introduces phi by genuine
naturality, and proves the trace square. There are no other sorry declarations
in this packet and no holes in definitions. The data module has zero holes.

Both new equations have the exact hypotheses of the source argument, including
arbitrary specified coefficient system and compactification. Checked their
zero-object, empty-scheme, dimension-zero and identity-arrow cases; all equations
reduce to the corresponding naturality or adjunction identities. They do not
assume finite-evaluation faithfulness or a Frobenius-stable rational lattice.

## No longer needed

Removed the item's former private imports of
`Mathlib.CategoryTheory.Adjunction.Basic`,
`Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
`Sheaf.Paper.TowerGeometricPurityMate`,
`Sheaf.Paper.TowerTracePurityComparison`, and
`Sheaf.Paper.SmoothPurityNormalizedEquivalence`.
The first two are supplied by the preserved public data imports. The tower mate,
trace comparison and normalized equivalence are needed by the new integral
lemmas' documented proofs, so they remain in those nodes' dependencies and are
not globally pruned. `Sheaf.SecSmoothPurity.SmoothPurityNaturality` is retained as
a private proof import of the item, rather than of the relocated data.

The old direct proof dependencies `lem-pur-tower-geometric-purity-mate`,
`det-sp-tower-gamma`, `lem-weil-pbc-adjunct-counit-identity`,
`lem-pur-integral-geometric-comparison-realization`, and
`det-sp-normalized-equivalence` now occur below the integral intermediate nodes.
`def-pur-tate-datum`, `def-pur-compact-support-transport`, `def-pur-smooth-trace`,
`thm-pur-rational-and-qbar-purity`, and `prop-pur-rational-purity-trace-coherence`
remain among the unchanged data's dependencies or public imports. The assembly
requires no direct projection-formula argument (`def-exchange-projection`):
projection enters only through the already specified purity constructions and
rational naturality/mate theorem. These are dependency relocations, not claims
that the library can discard those nodes.

No existing module is withdrawn. No source declaration is removed. No unit
statement or realized proof step is bypassed. Rational trace coherence and all
former public imports remain visible through the data module. The original
node's proof dependencies now track the four-clause assembly; deeper integral
dependencies have moved to the two integral nodes. No tool-use approvals were
removed, added or reordered. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The generic three-square argument does not need independent proofs of all three
squares: its third square follows by pasting naturality with the first two.
The node's original route expresses this fact, but it was not previously Lean
glue. The finite construction uses intrinsic-category purity naturality, so
one must explicitly transport across the equivalence units rather than treating
its statement as literal naturality of geometricPurityIso.

The integral realization and tower statements do not literally state the two
needed equations for the specified trace-transpose integralGamma and transported
integralBeta. The new nodes isolate precisely those identifications, including
tower_trace_purity_comparison; their proofs must take place on whole normalized
towers. No statement has been declared false or weakened.

The actual rational/common proof uses the existing
`lem-pur-rational-weil-naturality-mate`, which was already publicly imported but
was absent from the original node's proof dependencies. It is now explicit.
This is a coefficient naturality/mate tool for the exact canonical maps, not a
Poincare duality conclusion. The unit's general rational purity and trace
coherence statements do not directly give the arbitrary rational/common-arrow
equations in these coordinates; this existing lemma supplies precisely that
scalar-fraction descent. The integral trace-comparison node is likewise a
generic identification of the tower and trace-transpose purity families, not a
later theorem of another unit, and the unit contains no replacement equality.
Maintainer-owned tool_uses approvals have been left verbatim; if additional
cross-unit approval is needed for this existing lemma or for the integral trace
comparison route, the maintainer should record it.

A read-only audit of the deeper dependency closure also encountered an existing
DAG cycle outside this packet: `lem-pc-ring-hom-extension-differential` has
`lem-pc-ring-hom-extension-differential-adjacent` as a proof dependency, while the
latter has the former as a statement dependency. This packet changes neither
node. All four edited/new nodes were separately checked not to be reachable
from their own statement/proof dependencies. This is reported for maintainer
attention rather than repaired outside the assignment.

## New nodes

`def-pur-weil-equivariance-data` owns the unchanged thirteen definitions in
`Sheaf.Paper.WeilPurityEquivarianceData`. It introduces no mathematical data,
axioms or holes; its primary Lean signature is ThreeSquares.

`lem-pur-integral-equivariance-naturality` is Steps 2 and 5 of the original
source argument: realize tower purity naturality, identify the specified purity
using trace comparison, and compose actual support naturality. Its naturality
is stated on arbitrary arrows, independently of strict Weil data.

`lem-pur-integral-equivariance-mate` is Steps 1, 3 and 5: realize the tower mate's
counit equation and identify all completed geometric comparison maps. It is an
objectwise adjunction equation independently of the naturality lemma.

Change record: `coord/changes/E7-weil-equivariance-data.md`.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
