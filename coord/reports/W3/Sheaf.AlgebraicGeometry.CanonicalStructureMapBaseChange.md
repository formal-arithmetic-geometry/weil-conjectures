## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange,
AlgebraicGeometry.canonical_structure_map_base_change, with a complete Lean proof
from the new general single-module exchange comparison and the existing ordinary
unit identity in Scheme.Modules.moduleBaseChangeMap_algebra.

The proof supplies three proved private helpers: tensor_structure_transport,
single_pullback_naturality, and single_directImage_naturality. The first uses
Adjunction.homEquiv_leftAdjointUniq_hom_app to compare the tensor and ordinary
structure maps. The latter two follow from naturality of the selected derived
counit/right-derived unit and of the single-complex comparisons. The main argument
conjugates ordinary exchange by the tensor-to-ordinary pullback isomorphisms,
cancels the g comparison, applies the existing unit clause, and maps this actual
ordinary identity into the derived category. No signature, definition, public
import, or target statement changed.

Added Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison and its DAG node.
This is the remaining exchange-comparison step for an arbitrary module: it has
neither precomposition by the f structure map nor postcomposition by the p
structure map. Thus it isolates the exchange transport, rather than renaming the
original structure-map equation. Its docstring states a complete proof from the
existing derivedBaseChange_unit_compatibility, naturality, and the degreewise
single-complex identities. The statement was checked on zero modules, empty
schemes, identity squares, and squares without cartesianness: its argument uses
none of flatness, acyclicity, or invertibility of either single-module comparison.

Single-file compilation uses only lcompile.py. The combining module compiled
without warnings in 51.9 seconds; the final set and delivery probe are checked by
the dry run. Sources: Stacks Project Tags 08HY and 0096; Tag 08HY was also read
at https://stacks.math.columbia.edu/tag/08HY.

## Proved and sorry left

Closed by decomposition: AlgebraicGeometry.canonical_structure_map_base_change
(node lem-sc-canonical-structure-map-base-change), the one original hole.
There is no sorry in the item's module.

Added and left open:
AlgebraicGeometry.Scheme.Modules.canonicalSingleBaseChangeComparison
(node lem-sc-canonical-single-base-change-comparison), with its entire proof
exactly `:= by sorry` in its new module. This is one split-off hole, so the
closed-minus-added hole count of this decomposition is zero. All three private
helpers and the combination of the ordinary and derived identities are proved.
The existing hole derivedBaseChange_unit_compatibility is not changed or added.

## No longer needed

Removed import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose.
The node lem-pc-canonical-single-adjunction-transpose and its module are not
needed by this proof: the ordinary tensor-to-pullback structure transport follows
directly from Mathlib's leftAdjointUniq Hom-equivalence identity. Whether the
module becomes globally unreachable is for the maintainer's closure calculation.
No other node or module is claimed globally unnecessary.

Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility is no longer a direct
import of the item; it remains the planned proof dependency of the new exchange
comparison module, and is not pruned. The canonical pullback/direct-image
comparison nodes, ordinary module base-change algebra node, and tensor structure
sheaf node remain necessary. The existing public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false and no interface change was needed.
The old plan mentions canonicalSingleAdjunctionTranspose, but its use can be
replaced by the ordinary Mathlib leftAdjointUniq calculation. The DAG copy now
records the implemented naturality and ordinary-unit argument.

LeanFinder, Loogle, Mathlib grep, and searches in both library roots found no
existing pinned single-module exchange comparison theorem. LeanSearch returned
Internal Server Error; this is recorded as unavailable in the new node.

The local source checkout's Mathlib does not contain some single-complex
composition lemmas reported by the online Loogle search, so none was relied on
without checking. The generic comparison proof attempt reached the last
right-derived unit naturality rewrite but did not close the remaining comparison
normalization within the allotted proof-development portion. Its source proof,
not a partial Lean proof, is delivered for the next worker.

## New nodes

lem-sc-canonical-single-base-change-comparison, in
lean/Sheaf/AlgebraicGeometry/CanonicalSingleBaseChangeComparison.lean, records the
strict exchange-comparison part of proof step 1 of the original node. It uses
lem-pc-derived-base-change-unit-compatibility and the existing canonical single
comparison constructions. The ordinary structure-unit calculation and the
naturality calculations combining it with the target are already proved here.
The parent unit sk-prop-av-cube and its realized route are unchanged; this is
below that unit. No change record or forced adaptation is needed.

## Second reading by W3

1. I compared both delivered modules with the repository versions. The existing target and all
existing declarations retain byte-for-byte identical signatures; the only added declaration is the
explicitly documented split-off comparison theorem.

2. I compiled both modules with `lcompile.py --all`. They compile without errors or warnings. The
item theorem has no `sorry`; the split-off theorem is the sole named `sorry`, with no hollow
definitions, axioms, unsafe declarations, or forbidden implementation features. The axiom scratch copy confirms only `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx`: tensor_structure_transport and single_directImage_naturality have no `sorryAx`;
single_pullback_naturality inherits it from existing derived constructions, and both the item
and the split-off theorem have it as expected. No new axiom was introduced.

3. The split-off statement is a genuine arbitrary-module exchange compatibility result, strictly
more general than the structure-sheaf target and not a restatement of it. Its docstring gives the
source and a complete natural-language proof, and its DAG node records the exact signature,
dependencies, source, and proof route. Independent grep, LeanFinder and Loogle searches using
exchange/single-complex comparison terminology found no matching theorem. In zero-module cases
both sides are zero; in identity squares the identity exchange and inverse comparison cancellation
give the equation. Empty schemes cause no exception to these categorical identities. The source
[Stacks Tag 08HY](https://stacks.math.columbia.edu/tag/08HY) supplies the general mate construction;
the single-comparison identity follows by the recorded naturality and degreewise calculation.

4. The proof follows the shortest available route below the unit: ordinary module base-change
algebra, the canonical single comparisons, and naturality. It removes the unused
`CanonicalSingleAdjunctionTranspose` and direct `DerivedBaseChangeUnitCompatibility` imports from
the item; the latter remains an import of the split-off theorem. The unit's realized route and
statement are unchanged.

5. The DAG proof and dependency fields match the imports and declarations used by the Lean proof.
The new node is marked split and references the parent proof step; no target or definition was
changed.

I changed only the report by adding this second-reading record and explicit axiom/search evidence.
No mathematical repair was needed after compilation and comparison. The existing target docstring
still mentions canonicalSingleAdjunctionTranspose; the implemented proof instead uses the proved
tensor_structure_transport helper, as correctly recorded in the node and above. I leave that
existing docstring unchanged. The split comparison normalization is not a few-minute closure; the
first worker's scratch attempt and its remaining normalization step were inspected.
