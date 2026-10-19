## What changed

Proved `AlgebraicGeometry.etale_indEtale_weaklyEtale_comparison` in
`Sheaf.AlgebraicGeometry.EtaleComparison`, with its exact existing signature and all four
clauses. Clause 1 uses Mathlib's etale-to-weakly-etale instance. Clause 2 uses the already
proved `Algebra.IndEtale.weaklyEtale` instance and the recorded affine-spectrum equivalence.
Clause 3 follows the specified diagonal route: the source library already proves local
finite presentation of the diagonal, then Mathlib's flat locally finitely presented
monomorphism theorem makes it open, and the etale criterion finishes. Clause 4 uses the
already proved `WeaklyEtale.hasRingHomProperty`; the proof explicitly converts its ring
property into the two flatness conditions for exactly the appLE-induced algebra.

Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` and removed the
unused proof imports listed below. All existing public imports and every declaration's
visibility and type are preserved. Updated the theorem's proof explanation and the node's
proof, proof dependencies and proof origin to match the actual argument. No definitions or
statements changed; no consumers need adaptation.

The module compiled cleanly after import pruning. The clause-4 algebra structure is installed
from the chart homomorphism itself, so the multiplication map is the one in the statement.
No finiteness or nonemptiness hypotheses have been introduced. In particular the zero ring,
empty affine opens, and schemes without quasi-separatedness remain covered.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.etale_indEtale_weaklyEtale_comparison`
(node `det-pe-morphisms-etale-comparison`). All four conjuncts are proved.

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Holes left in the delivered module: 0.
No new declarations with sorry are delivered.

Revalidated on 2026-10-19 against the published server build: the identical proof with
`#print axioms` compiled in 2.4 seconds. The theorem and the three source APIs
`WeaklyEtale.hasRingHomProperty`, `locallyOfFinitePresentation_diagonal`, and
`Algebra.IndEtale.weaklyEtale` use only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed these direct proof imports:

- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.AlgebraicGeometry.PullbackCarrier`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.RingTheory.FinitePresentation`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`
- `Sheaf.RingTheory.IndEtaleUniverseTransport`

The Mathlib infrastructure above remains available through the imports the statement and
actual proof require. The large principal-Zariski stability conjunction is unnecessary:
its ind-etale-to-weakly-etale clause is already a proved source instance exposed by the
existing public imports. The separate unramified-morphism bundle is unnecessary because
Mathlib supplies the formally unramified criterion directly. The universe-transport module
is unnecessary because the statement uses two rings in the same universe and the existing
ind-etale instance applies directly.

Removed these direct proof dependencies from the node:

- `lem-weil-pbc-open-fibre-product`: the existing affine ring-property comparison already
  performs the local diagonal identification.
- `lem-weil-pbc-fibre-product-affine-spectra`: the source's spectrum equivalence and ring
  comparison already provide this calculation.
- `def-weil-affine-spectrum`: remains a statement dependency; no separate proof step needs it.
- `lem-weil-pbc-flat-morphism-affine-criterion`: subsumed by the existing weakly-etale
  ring-property API.
- `lem-weil-pbc-flat-ring-map-iff-flat-affine`: subsumed by the recorded spectrum comparison.
- `def-weil-flat-morphism`: flatness is supplied by the weakly-etale instance and the cited
  flat-monomorphism theorem; no separate local-flatness proof remains.
- `def-weil-unramified-morphism`: use Mathlib's formally unramified criterion directly;
  the separate conjunction definition is unnecessary.
- `def-weil-open-immersion`: open immersion is supplied directly by the retained
  `lem-pe-flat-lfp-monomorphism-open` Mathlib leaf.
- `lem-weil-pbc-ind-etale-stability`: reuse the source instance directly, avoiding the bundle.
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`: the already proved source diagonal
  theorem avoids redoing the chart presentations.
- `def-weil-pbc-finitely-presented-algebra`: no explicit finite presentation construction
  is needed after reusing the proved diagonal theorem.
- `def-weil-finite-type-morphism`: the final etale criterion directly uses formal
  unramifiedness, flatness and the original local finite presentation.

No module is withdrawn. These nodes need no further direct work for this theorem; this does
not assert that their modules have no other consumers or leave the full target closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The planned seven-step proof expands arguments
already proved in the source library. Its flat-monomorphism diagonal route is retained,
with local finite presentation of the diagonal obtained from the existing cancellation
lemma rather than a new finite-generator calculation. The existing affine ring-property
comparison already supplies both directions of clause 4.

Searches: local rg located the source APIs; msearch Loogle and grep returned the Mathlib
weakly-etale instances and definitions. Lean Finder was also queried. No new split is needed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
