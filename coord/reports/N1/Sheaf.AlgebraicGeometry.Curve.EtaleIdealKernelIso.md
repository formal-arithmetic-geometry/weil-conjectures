## What changed

Proved `AlgebraicGeometry.Scheme.exists_etaleIdealKernelIsoPair` with its signature and
visibility unchanged. Added the proved module
`Sheaf.AlgebraicGeometry.Curve.EtaleIdealSectionsKernel`, which constructs canonical
ideal-section inclusions and proves their sectionwise kernel property. The assigned
module imports it only for the proof. All original public imports are retained.

The geometric proof uses the existing flat module pullback exactness and
closed-subscheme base-change ideal-image declarations. The combining proof constructs
presheaf kernels, applies left-exact sheafification, transports by its counits, and
proves the nested-inclusion equation by functoriality. Every construction uses specified
maps or inverses uniquely determined by their properties. No interface of an existing
module changed and no forced adaptation is needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_etaleIdealKernelIsoPair`
(node `lem-sc-etale-ideal-kernel-iso`).

Also proved the new public theorem
`AlgebraicGeometry.Scheme.etaleIdealSectionsInclusion_isKernel`
(node `lem-sc-etale-ideal-sections-kernel`), and all private helpers.
Holes added: zero. Sorries left in either delivered module: none.
The proof uses existing dependencies which can still rest on sorries; this is a proof
from existing stated declarations, not a decomposition introducing further holes.
Both modules compile locally as one import-ordered set.

## No longer needed

No original import is removed. The old proof dependency `def-pc-module-pullback` is no
longer directly used by the target proof; the new sectionwise node records the geometric
pullback argument. Every original import is needed by the existing signature. In particular,
`EtaleTensorSectionsRightExact` supplies the tensor-sections functor used in the signature;
its right-exactness theorem is not invoked, but the module cannot be pruned.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or interface error was found. The original single proof
paragraph combined the geometric section calculation with categorical glue; the updated
DAG records their actual separation and the proved sectionwise node.
`blueprint_refs.py ancestor lem-sc-etale-ideal-kernel-iso` returned no ancestor because
of the existing indirect reference chain. The new node explicitly records the source
blueprint `lem-sc-brauer-zero-all-curves`, Step 1 and its Claim, as named in the original
module and node. The blueprint search for `ideal kernel` found no existing match.
The source literature body is absent from this machine; the proof is derived from the
already formalized dependency statements and their recorded sources.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and grep searches succeeded.
The new proof uses the flat-pullback exactness and closed-subscheme ideal-image nodes
from other units as general tools; no node of this unit already states those general
facts. Their module signatures and proofs were read, and both imports pass the project's
import-direction check.

## New nodes

`lem-sc-etale-ideal-sections-kernel`, in
`dag/nodes/sec-curve-estimates/lem-sc-etale-ideal-sections-kernel.json`, records the proved
sectionwise kernel theorem. It is strictly smaller than the assigned statement: a single
etale object's additive groups, without sheafification, global kernel isomorphisms or
nested-inclusion compatibility. Its canonical maps are explicitly constructed.
Edge cases checked in the argument: empty scheme/object, zero and unit ideals, and equal
nested ideals. All follow from the same flatness, image and kernel constructions.
No change record is required because existing statements and definitions are unchanged.

## Second reading by N1

1. Compared both delivered modules and the existing target module against the repository
versions. Existing declaration signatures are unchanged; the only added declaration is the
new split-off kernel theorem recorded in its node.
2. Compiled the two modules in import order with `lcompile.py`; both compile without errors.
Searched delivered files for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and
`implemented_by`; none occur in declarations. The proof uses only existing imported results.
3. Checked the split-off theorem against its node and source: it is sectionwise and strictly
smaller than the target, with no added hypotheses beyond the stated scheme, ideal, and etale
object. Its docstring and DAG proof explain the construction and edge cases.
4. Read the proof downward and checked the shortest available route: the sectionwise kernel
node supplies the geometric calculation, then presheaf limit reflection and left-exact
sheafification supply the categorical glue. The new module's tensor-pullback import is public
because its declaration is used in the public inclusion definition; no unused proof import was
found. The target unit route and realized steps remain represented.
5. Compared the DAG proof and `proof_deps` with the Lean proof. The target node now records the
sectionwise split, sheafification transport, and inclusion compatibility steps, and the new
node records its own dependencies and source. No existing target statement or definition changed.

Changed during this reading: completed the report with the independent review and identified
`def-pc-module-pullback` as an old proof dependency no longer directly used. Tested making
`TensorPullbackStructureSheaf` private; compilation fails because the public coordinate
definition uses it, so retained the original public import. No Lean or node change was needed.
