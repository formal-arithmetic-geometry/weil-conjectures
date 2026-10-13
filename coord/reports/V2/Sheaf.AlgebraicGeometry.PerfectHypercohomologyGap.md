## What changed

Proved `AlgebraicGeometry.perfect_hypercohomology_gap` with its signature and visibility unchanged.
Added a proved private helper `tensor_single_homology_vanishes` converting the existing
existential module-tensor vanishing predicate into vanishing for the canonical derived tensor.
The proof uses the source library's finite Tor amplitude bounds and the canonical truncation
triangle at `j-b`: its lower piece tensors into degrees at most `j-1`, and its upper piece
into degrees at least `j+1`. The homology exact sequence gives the result.
The original declaration docstring retains the original spectral-sequence plan;
the updated DAG proof and this report describe the implemented shorter route.

Only two proof imports remain: `Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison` and
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`. Both statement imports remain.
The DAG route is updated and four records attach already proved generic source declarations.
No new Lean module, statement, axiom, definition, or interface change is introduced.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.perfect_hypercohomology_gap`
(node `lem-sc-perfect-hypercohomology-gap`). The private helper is also fully proved.
No sorry remains in the delivered Lean file; no sorry was added. This is a proof, not a
hole decomposition. Dependencies can still carry their existing holes; no claim is made
that the whole target import closure is axiom-free.
Compilation: `lcompile.py` passed cleanly, with no warnings, in 41.5 seconds.
The public theorem's unused-hypothesis linter is locally disabled: the stronger source
Tor bounds need neither perfection nor quasi-coherent cohomology, but the signature stays fixed.

## No longer needed

Removed proof imports:
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`.
- `Sheaf.Algebra.Homology.KFlat` (available through the necessary statement imports).
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`.

Original planned dependencies no longer used as proof steps:
- `def-pc-perfect-complex`: no local strictly perfect model is needed. Its module stays
  publicly imported because the existing statement uses `X.IsPerfect`.
- `def-pc-flat-sheaf-modules` and its module
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`: no sheaf-flatness API is used directly.
- `lem-pc-bounded-above-flat-kflat` and its module
  `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`: the proved generic source
  categorical bounded-flat theorem is used instead.
- `thm-sp-spectral-object-yields` and its module
  `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`: no filtered complex,
  spectral sequence, pages, convergence or finite-filtration argument is constructed.

`def-pc-kflat-complex` and `def-pc-tensor-complex-sheaves` still enter through the tensor
vanishing predicate and K-flat comparison. They are not globally prunable.
Removed direct imports do not assert that their modules are absent from all transitive
closures; pruning is specific to this proof route. No unit's own statement or realized
proof step was bypassed: `dag/units/sk-thm-picard-duality.json` has no realized entries
for this below-unit auxiliary gap lemma.

## Where the brief, the DAG or earlier work was wrong

The DAG plan overlooks the already proved generic source tensor-bound lemmas in
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`. They give a shorter complete
proof by one truncation triangle; no new spectral-sequence bridge is necessary.

The upstream global `DerivedCategory.commShiftTensorLeft` and `isTriangulated_tensorLeft`
instances tie the Grothendieck universe to the chosen derived-category universe, whereas
this statement has independent `uG,wG`. No upstream signature was changed. Use the
proved `commShiftTensorLeftQhObj` and `isTriangulated_tensorLeftQhObj` with a bounded flat
model and transport along its representing isomorphism. This proves exactly the
triangulatedness needed at the existing universes.

Edge cases checked: no assumption `a ≤ b` occurs in the proof. If `a>b`, the interval
is empty and the source Tor test still implies the tensor bounds. For `a=b`, the gap
has one degree and the truncation arguments give the same strict bounds. Empty schemes,
zero objects and unbounded L need no special hypothesis. The proof never assumes QCQS,
affine covers or boundedness of L.

Searches were run through msearch (logged in searches.jsonl): LeanFinder returned
only t-structure/Tor facts; Loogle found the total tensor API but no Tor-amplitude
statement; grep found no generic Tor-amplitude bounds in Mathlib. LeanSearch returned
HTTP 500, recorded as unavailable. Searches of the whole blueprint for `tensor cohomology`,
`09M4`, `bounded flat model`, `Tor amplitude`, and `triangulated tensor`, and text searches
of the DAG and library, found no record of the four generic source interfaces below.
The ring-specific flat-model and tensor-computation nodes have different statements.
The source of the original argument was read at https://stacks.math.columbia.edu/tag/09M4.

## New nodes

`lem-sc-source-tor-amplitude-flat-model` attaches the existing proved
`DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn` (FlatModel.lean:260).
Its generic categorical statement, unlike the existing ring-specific flat-model node,
applies directly to the sheaf-module category. No sorry is introduced.

`lem-sc-source-tor-amplitude-upper-tensor-bound` attaches the existing proved
`DerivedCategory.isLE_tensor_of_torAmplitudeIn` (FlatModel.lean:430), used on the lower
truncation piece. No sorry is introduced.

`lem-sc-source-tor-amplitude-lower-tensor-bound` attaches the existing proved
`DerivedCategory.isGE_tensor_of_torAmplitudeIn` (FlatModel.lean:453), used on the upper
truncation piece. No sorry is introduced.

`lem-sc-source-kflat-tensor-left-triangulated` attaches the existing proved
`DerivedCategory.isTriangulated_tensorLeftQhObj` (Monoidal/Shift.lean:161), with its
source shift comparison, to transport distinguished triangles at independent universes.
No sorry is introduced. All four records have `existing: true`, the same chapter/unit
as the item, and the nearest blueprint ancestor `lem-sc-finite-duality`.

There are no change records or forced adaptations.

## Second reading by V2

1. **Unchanged interface — pass.** Read the entire delivered module and its repository
   diff. Programmatically compared the complete original theorem signature through
   `:= by`: byte-for-byte identical. Existing docstrings and both public imports are
   unchanged. Only a private proved helper, local proof options, proof imports and the
   proof body were added or changed. There are no definition or statement changes,
   change records, or adapted modules.
2. **Kernel proof — pass.** Recompiled the delivered file cleanly with `lcompile.py`
   (48.0 seconds). Compiled a scratch copy with `#print axioms` for the public theorem,
   private helper and all four attached source theorems (49.7 seconds). Every result
   lists only `propext`, `Classical.choice`, `Quot.sound`; none lists `sorryAx`.
   Scanned the source: no sorry, axiom, unsafe, opaque, implemented_by or extern.
   Representatives are eliminated inside proofs of propositions; no data definition
   chooses an arbitrary witness from an unproved existence theorem.
3. **Split statements and reuse — pass.** No statements were split off and no holes
   were added. Read each of the four new DAG attachments against the existing proved
   source declaration and its ambient assumptions. They record reusable generic
   categorical results, not new Lean declarations or disguised restatements of the
   gap theorem. Checked zero objects and a singleton amplitude; for reversed bounds,
   the Tor test forces a zero object and the truncation proof still works. Independent
   searches used the phrases "derived tensor preserves a missing interval of
   cohomology via truncation" (LeanFinder), `"homology", "tensor"` (Loogle), and
   library/DAG ripgrep searches for the generic source bounds and triangulated tensor.
   No shorter applicable gap theorem or pre-existing attachment was found.
4. **Shortest route and pruning — pass.** The K-flat comparison converts the Tor
   test; the triangle at `j-b` gives A <= j-b-1 and B >= j-a+1. The two source tensor
   bounds give outer homology zero in degree j, so exactness gives the desired zero
   middle homology. The final comparison proves the original existential predicate.
   Both remaining proof imports are used; public imports support the unchanged
   signature. Compared old proof_deps with the report: all four abandoned planned
   dependencies are accounted for, and the K-flat/tensor definitions remain in use.
   Read `dag/units/sk-thm-picard-duality.json`: this auxiliary node realizes no fixed
   unit statement or step, so this below-unit shortening preserves the unit route.
5. **DAG agreement — pass.** Read all five delivered nodes;
   the item's proof steps, dependency union and proof_origin follow the actual Lean
   argument. The four new records attach existing source declarations with creation,
   source, search, blueprint, chapter/unit and Lean metadata. Verified their source module paths. The first dry run clarified that
   `lean.existing: true` records must omit `lean.file`; removed the fields I had
   temporarily added. No metadata change remains. Historical split_report/tool_uses in the existing node are
   prior-stage records, not the newly delivered proof route.

Second-reading changes: added this review section; retained the original Lean proof
and node records after validation. No Lean proof repair was needed. Confirmed holes closed:
`AlgebraicGeometry.perfect_hypercohomology_gap` (1); holes added: none (0).
