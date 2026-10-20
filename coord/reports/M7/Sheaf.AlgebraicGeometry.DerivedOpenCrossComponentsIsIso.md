## What changed

Retire the already-proved duplicate module
Sheaf.AlgebraicGeometry.DerivedOpenCrossComponentsIsIso using deleted.txt. Reattach
lem-sc-derived-open-cross-components-iso to the existing declaration
AlgebraicGeometry.derived_open_cross_components_isIso in
WeilConjectures.AlgebraicGeometry.DerivedOpenCrossComponentsIsIso. This is the
shortest route: the adopted theorem already proves exactly the needed proposition.
The mathematical statement, proof steps, proof dependencies, and unit route are retained.
No adopted source file changes.

Read the original theorem and its node, the single-intersection-mate theorem and node,
the restriction-map definitions, the sole parent node and its Lean consumer, and Stacks
cohomology.tex lemma-restrict-direct-image-open (08FE) and lemma-glue (08DG). The
upstream proof applies the mate theorem on U, applies it with exchanged opens on V,
and factors the other component through direct image of c by adjunction naturality.
The same arbitrary adjunctions, unbounded categories, and universes occur in both
versions. No cover assumption is introduced, so disjoint and empty opens are included.

Validation: the original module compiled with zero holes. A temporary signature probe
imports only the adopted replacement (besides the original public restriction-map
import) and proves the original type by exact application of the upstream theorem,
including its unused rW let-binding. The upstream theorem's printed axioms are exactly
propext, Classical.choice, and Quot.sound. A temporary copy of the unchanged parent
RelativeOpenDifferenceDiagram is also compiled against the upstream theorem. Scratch
probes are not delivered. No declaration is replaced by an unproved statement.

Change record: coord/changes/M7-derived-open-cross-components-retire.md.

## Proved and sorry left

Actual initial holes in the item: zero. Holes closed: zero. Holes added: zero.
Split-off statements: none. Sorries left in delivered modules: none.
AlgebraicGeometry.derived_open_cross_components_isIso was already proved in both
copies; its adopted proof is retained and independently checked against the old type.
This delivery is duplicate retirement, not a new proof or a decomposition.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.DerivedOpenCrossComponentsIsIso, including its
duplicate declaration and its public import of
WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps and private import of
WeilConjectures.AlgebraicGeometry.DerivedOpenIntersectionMateIso. Both dependency
modules remain needed by the adopted proof and are not withdrawn. No DAG node or
mathematical proof dependency is pruned; the existing node is realized upstream.

No current Lean module imports the retired Sheaf path. The sole DAG parent,
lem-sc-relative-open-difference-diagram, is attached to
WeilConjectures.AlgebraicGeometry.RelativeOpenDifferenceDiagram, which already imports
the adopted replacement and applies it at line 228. No quarantined module refers to
the retired path or declaration. Thus the actual replacement argument is the unchanged
complete upstream proof, and the DAG attachment update preserves the unfinished-parent
interface as well. No parent dependency or consumer edit is necessary. The unit record
sk-thm-picard-duality does not assign a realized statement or proof step to this module.

## Where the brief, the DAG or earlier work was wrong

The assigned source has no sorry and already compiles, contrary to the generic proof
brief's premise. coord/retire-items.tsv explicitly lists it for retirement. Its historical
DIFFERENT classification cited foundational Sheaf imports, but these imports have since
been migrated to the adopted source, and the current types agree definitionally. The
only textual signature difference is an unused rW let-binding in the Sheaf copy.
The DAG attachment still named this redundant copy while its sole parent already used
the adopted theorem. This delivery reconciles that attachment; it does not hand the
obligation to another worker. No new nodes or assumptions are introduced.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
