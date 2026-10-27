## What changed

Proved `WeilConjectures.IntegralSystemRealization.constructibleReduction_good` with
its existing signature. The proof imports IntegralResidueTor,
FiniteRingConstructibleDerivedOrigin, ProEtaleBoundedConstructibleTriangulated,
and DirectImagesConstructible privately. ZetaSeries is imported privately for the
base-field-to-residue-field map. Private proved helpers transport the three
finite-level predicates and assemble compatible origins for every system satisfying
LevelBounds. Updated the existing node proof, proof_deps and proof_origin.

Normalization is the recorded calculus field. Integral constructibility provides one
cohomological interval, and the existing residue-Tor theorem provides the same Tor
interval. Both are transported through the actual reduction-evaluation isomorphisms.
Finite-ring constructible descent supplies the etale antecedents. Their comparison
images serve as fixed-scalar levels. Fullness of the realization equivalence and the
bounded-below comparison Hom bijection lift the actual system transitions, proving
both transitionSquare and originSquare. No derived morphism equality is inferred
from separate finite evaluations.

## Proved and sorry left

Closed the sole hole: `WeilConjectures.IntegralSystemRealization.constructibleReduction_good`
(node lem-sf-constructible-reduction-good). Added zero holes; zero holes remain in
the item. All private helpers are proved. This is a proof from existing declarations,
not a decomposition. Imported declarations retain their own existing dependencies.
The final file passed server compilation cleanly in 23.3 seconds. A proved generic
categorical cancellation helper completes the origin square without fragile rewriting.

## No longer needed

The direct proof does not use node lem-weil-pbc-normalized-etale-origin-witnesses or
module Sheaf.Paper.NormalizedEtaleOriginWitnesses: Origins asks for adjacent
restriction maps and their image equations, not the full scalar-extension
normalization cocycle. The bounded-below comparison Hom bijection lifts these maps
directly. This unused dependency was removed from proof_deps; its module was never
imported here. No existing public imports or declarations are removed, and no module
is withdrawn. The unit route is unchanged.

Searches: msearch leanfinder returned generic derived-category representatives;
loogle returned no hits for the exact-functor equivalence query; grep returned no
Mathlib hits for FixedEtaleOriginWitness or IsNormalizedCoefficientSequence.
Local searches found and reused the published coefficient calculus, residue-Tor,
finite-ring descent and bounded-below Hom comparison declarations.

## Where the brief, the DAG or earlier work was wrong

The original node plan used the stronger normalized-origin witness theorem.
The actual Origins interface only needs maps into restrictions of bounded-below
etale objects. Exact restriction preserves this bound, so full comparison lifts
the maps directly, without normalization isomorphisms or their cocycle. The
statement is unchanged. Zero objects and empty schemes are covered by the same
finite-ring descent and Hom-lifting arguments; no positive-rank or finite-type
hypothesis is introduced.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
