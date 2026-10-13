## What changed
The item's unchanged theorem is reduced by `constructor` to its two conjuncts,
`picardExternal_right_cech_tensor_exact` and
`picardExternal_right_cech_product_exact`, in two new modules imported only for
the proof. Each component is strictly part of the original assertion: neither
asserts the other functor's short exactness. This is a decomposition, not a net
proof gain. No existing signature, definition, visibility, or public import changes.
The identical copy of PicardExternalRightCechModels was removed from the delivery.

## Proved and sorry left
Hole closed: `AlgebraicGeometry.Scheme.Modules.picardExternal_right_cech_exact`
(1 of 1 original holes), conditional on the two component theorems below.
Holes added and left:
- `AlgebraicGeometry.Scheme.Modules.picardExternal_right_cech_tensor_exact`, node
  `lem-sc-picard-external-right-cech-exact-tensor`.
- `AlgebraicGeometry.Scheme.Modules.picardExternal_right_cech_product_exact`, node
  `lem-sc-picard-external-right-cech-exact-product`.

Thus one hole is closed and two are added (net -1 before any closure pruning).
No component hole was closed in the second reading. This is not a sorry-free
proof of the item. All three declarations compile; the scratch `#print axioms`
check finds only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for
all three declarations. The delivery tool repeats
its own declaration probes.

## No longer needed
No imports or library modules are pruned. The original public imports of the
model and affine-morphism modules remain necessary for the signatures.
The parent's old direct proof dependencies are no longer used directly:
`lem-sc-picard-affine-diagonal-intersections`, `pqf-lem-affine-vanishing`,
`lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-module-pullback-affine-sections`, and
`lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`.
They remain dependencies of the component arguments and are not pruned from the
DAG. The parent's proof_deps now names exactly the two components it applies.

## Where the brief, the DAG or earlier work was wrong
The draft delivered valid component signatures but incomplete documentation and
node records: placeholder Lean statements, absent searches, and proof steps
citing the parent while proof_deps was empty. Such parent citations would make
the decomposition circular. The parent itself still recorded its old plan.
The second reading repairs these faults, records full independent component
arguments, and explicitly accounts for both added holes. The affine section,
tensor-total and product-section formalizations remain substantial; they were
not closed merely by applying a generic Mathlib lemma.

## New nodes
`lem-sc-picard-external-right-cech-exact-tensor`, module
`Sheaf.AlgebraicGeometry.PicardExternalRightCechTensorExact`, isolates the
tensor-total conjunct. Its independent plan uses affine intersections and affine
vanishing, then exactness of tensor over a field and degreewise exactness.

`lem-sc-picard-external-right-cech-exact-product`, module
`Sheaf.AlgebraicGeometry.PicardExternalRightCechProductExact`, isolates the
product-cover conjunct. It additionally uses affine fibre-product, pullback,
and tensor section formulas. Both nodes have verbatim signatures, self-contained
statements, the search records, source, and parent blueprint provenance.
No statement/definition changes or change records are needed.

## Second reading by R1
1. Compared every existing delivered module with its repository version. The
   parent differs only in its proof and two plain proof imports. Its signature
   is byte-for-byte unchanged. The models copy was identical and is omitted.
   New modules contain statements and named proof holes, with no data definitions.
   Verdict: no accidental interface change.
2. Compiled all three final modules through lcompile.py, without warnings.
   Inspected for forbidden declarations and proof bypasses; none occur. The only
   sorries are the two listed component theorems. Scratch #print axioms checks
   show only the standard axioms and the expected sorryAx. Verdict: valid
   conditional proof, honestly recorded as a decomposition.
3. Read both component signatures against the definitions and Stacks Tag 0BED
   (https://stacks.math.columbia.edu/tag/0BED, coefficient diagram and the
   right-variable argument). In degree n the tuples have n+1 entries, so no
   intersection of an empty family is invoked. Empty indexing types give zero
   terms, empty opens have zero sections, repeated opens cause no exception, and
   tensor with a zero module is zero. No cover condition is used, and tensor is
   over the field, so F need not be flat over O_X. Each component proves just one
   conjunct. Searches with new terminology through leanfinder, loogle and local
   rg found generic exactness tools, not duplicate component theorems. The
   existing left-variable theorem is still sorry and uses fixed finite
   subcovers. Verdict: true, strictly smaller components, still unproved.
4. Inspected from the parent down and reviewed possible reuse of
   TopCat.Sheaf.shortExact_cechComplex and
   HomologicalComplex.shortExact_iff_degreewise_shortExact. They do not supply
   the missing affine scalar-section and external-section identifications.
   All imports are needed by signatures or proofs. The old direct dependencies
   are fully listed above and retained below the split. Inspected
   dag/units/sk-prop-av-cube.json: its realized fields are empty in the baseline;
   this below-unit coefficient decomposition changes none of its statement,
   steps, cited units or realization records. Verdict: route retained; no pruning.
5. Checked both new node records and repaired their proof dependencies to the
   union of step uses, with no edge back to the parent. The parent now records
   precisely the two theorem applications. LeanSearch was also attempted and returned Internal Server Error; its unavailability
   is recorded without claiming a mathematical search result. Full signatures, source and searches
   replace the placeholders. Verdict: DAG agrees with Lean.

Changes made by second reading: expanded both docstring proofs and fixed line
lengths; completed both new nodes and their search records; corrected the
parent proof/dep/origin records; omitted the unchanged models file; corrected
hole accounting and pruning report. The original reduction proof is retained.
