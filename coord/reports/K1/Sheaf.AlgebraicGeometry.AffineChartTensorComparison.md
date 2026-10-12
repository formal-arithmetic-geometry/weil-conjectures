## What changed

Proved `AlgebraicGeometry.exists_affineChart_tensorComparison` with its signature unchanged.
Constructed the fixed coordinate rings, their transported R-algebra structures and the
finitely presented appLE algebra map. Defined the restricted base-changed morphism using
resLE and proved its tensor-arrow comparison by the two pullback projections.

Added the proof-only import `Sheaf.AlgebraicGeometry.AffineChartBaseChangeIso`.
That new module proves `AlgebraicGeometry.exists_affineChart_baseChangeIso`, identifying
one base-changed chart with Spec(A ⊗[R] B), with both projections specified.
It uses only Mathlib and contains no sorry. All original public imports are retained.
Updated both DAG proof records to match these proofs.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.exists_affineChart_tensorComparison`
(node `lem-weil-pbc-affine-chart-tensor-comparison`).
Also proved `AlgebraicGeometry.exists_affineChart_baseChangeIso`
(node `lem-weil-pbc-affine-chart-base-change-iso`).
No sorry remains in either delivered module; no holes were added or split off.
Local compilation of both modules passes without warnings. `#print axioms` for both
declarations lists exactly `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`.

## No longer needed

No imports or modules are pruned. The original affine-open, morphism-to-Spec and
finite-presentation nodes remain used. The old direct proof dependencies
`lem-weil-pbc-open-fibre-product` and `lem-weil-pbc-fibre-product-affine-spectra`
move into `lem-weil-pbc-affine-chart-base-change-iso`; both remain transitively used
through the new proved helper, rather than directly in the original module. Their mathematical arguments remain necessary; neither is claimed
as pruned. The unit's realized nodes and route are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan is sufficient. The one-chart geometric
identification required an explicit assembly of Mathlib's open pullback image formula,
isomorphism of equal-range open immersions and pullbackSpecIso projection equations.
The helper isolates and fully proves that assembly rather than postponing it.

LeanFinder and Loogle found these ingredients but no combined result. LeanSearch
returned Internal Server Error and is recorded as unavailable. Grep and blueprint
search found no duplicate combined projection-compatible chart statement.
Stacks Tags 01JR and 01I4 were read on their public tag pages; the local literature
copy is absent on this machine. The zero-ring and empty-chart cases use the same
pullback and spectrum identities, with no nonempty assumptions.

## New nodes

`lem-weil-pbc-affine-chart-base-change-iso`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-chart-base-change-iso.json`,
records the fully proved single-chart identification and both projection equations.
Its module is `Sheaf.AlgebraicGeometry.AffineChartBaseChangeIso`.
It is a strict geometric part of the original argument, with no finite-presentation
assumption or morphism between two charts, and introduces no sorry.

## Second reading by K1

1. PASS: Compared the delivered tensor-comparison module with the repository using
   diff. Its existing declaration signature and docstring are byte-for-byte unchanged;
   the only changes are the proof and a plain proof-only helper import. The helper
   module is new. No definition or existing statement changes; no change record needed.
2. PASS: Compiled both modules in import order with lcompile.py, without errors or
   warnings. Scanned both sources for sorry and forbidden declarations/attributes: none.
   Scratch-copy `#print axioms` for both public theorems lists exactly propext,
   Classical.choice and Quot.sound. Coordinate rings and algebra structures are
   constructed from sections and actual maps; no arbitrary witness of an unproved
   existence theorem is used.
3. PASS: No sorry statement is split off. Read the new helper's signature, word proof
   and node together: it proves a strictly smaller one-chart geometric assertion,
   without finite presentation or the morphism between two charts. Checked empty V,
   empty t⁻¹(W), zero coordinate rings, and identity base change: range intersection,
   open-immersion identification, and tensor-pullback identities cover these cases
   with the same projection equations and no nonempty assumptions. Independent
   LeanFinder, Loogle and local searches found ingredients (including
   pullbackRestrictIsoRestrict), but no duplicate combined projection-compatible
   statement or shorter route that removes the required assembly.
4. PASS: The main proof constructs the fixed algebra map, proves finite presentation
   directly by Mathlib's finitePresentation_appLE, and compares both pullback
   projections. The helper also uses proved Mathlib results only. All imports are
   needed: the three original public imports supply the statement's finite-presentation,
   Over.pullback and tensor-map vocabulary; the helper's public Pullbacks import
   supplies the scheme pullback instances and tensor-spectrum vocabulary, while
   PullbackCarrier and the helper import itself are proof-only. No module is pruned.
   Clarified that the two removed direct DAG dependencies remain used transitively.
   Read dag/units/sk-thm-p1.json realized; no unit statement or step is bypassed or changed.
5. PASS: The existing node changes only proof, proof_deps and proof_origin. Checked
   each step and its dependency against the Lean and the Mathlib matches of the
   older nodes; proof_deps equals the union of uses. The new node has the required
   provenance, searches, source, chapter/unit, blueprint and Lean record, whose
   statement matches its actual theorem signature exactly.

Second reading changed only this report (including the explicit dependency names)
and the new helper node's grep-search evidence, replacing unrelated broad-search hits
with the relevant declarations read locally. No Lean proof repair was needed.
Closed one original hole; added zero holes; additionally delivered one fully proved helper.
