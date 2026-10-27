## What changed

Filled `AlgebraicGeometry.Scheme.limitScalarChainComparison` without changing any
public signature. Private helpers construct the scalar comparison
from the normalized extension/restriction adjunction and the sectionwise site
equivalence. The proof first verifies the coefficient square by limit projections,
then lifts the module comparison termwise and proves both tensor formulas,
homotopy naturality, and uniqueness. The DAG proof now follows this construction. Private instances cache zero-morphism
preservation and countable ring-sheaf limit synthesis. The three proved additivity instances
expose the additivity used by the homotopy clause. The three functors `scalarChainTransport`, `scalarChainLeft`, and
`scalarChainRight` are ordinary definitions to avoid repeated elaboration of their
large bodies. Transport uses the inverse of the supplied coefficient isomorphism
directly; inverse uniqueness identifies it with the original expression. All
public signatures and the mathematical functors remain unchanged. The change
record is `coord/changes/P7-limit-scalar-chain-transport.md`; downstream checks
find no external Lean consumers, so no forced adaptations are needed.

The source read was Stacks `sites-modules.tex`, Tag 03EL,
`lemma-tensor-product-pullback` (the Hom/adjunction proof), and Section 03EK,
`section-tensor-product`. Searches used LeanFinder, Loogle, and grep through
`msearch.py`, plus direct searches of Mathlib and both library roots.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.limitScalarChainComparison`
(node `lem-weil-isomorphism-limit-scalar-chain-comparison`), the item's sole hole.
Added: no holes. Remaining in the item: none. No statements were split off. The final module compiles cleanly through
`lcompile.py` in 47.4 seconds, with no warnings. Delivery preflight also checks
the complete packet.

## No longer needed

Removed private import
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` and proof dependency
`lem-pur-proetale-inverse-image-tensor-comparison`: the scalar extension adjunction
constructs the normalized comparison directly. Its top-level tool-use approval
is removed from the node. The generic inverse-image tensor theorem itself remains
untouched and may still be needed by other consumers.

The proof does not use `def-pc-tensor-complex-sheaves`' direct-sum total tensor API:
the stated functors already apply ordinary scalar extension termwise.
`def-pur-sheaf-tensor-product` is not needed as a separate proof dependency;
`extensionFunctor` and `extensionTmul` already provide the actual tensor and
sheafification. Both remain statement dependencies where already recorded.
No module is withdrawn; all public imports are retained.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The original node planned to compose with the general
inverse-image tensor comparison. Its adjunction argument specializes directly to
the canonical sectionwise model and avoids that extra dependency. The module's
own definitions already implement the degreewise extension, so a total-tensor
identification is unnecessary. The chapter and unit route are preserved.

The restriction square leaves local elements unchanged; its linearity is exactly
`cR.inv ≫ F.map jY = jX ≫ cS.inv`. The unit normalization proves the tensor rule
first at scalar one, then at arbitrary scalars by linearity. This also handles
zero rings, zero modules, identity coefficient maps, non-flat coefficient maps,
and unbounded complexes without extra hypotheses.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
