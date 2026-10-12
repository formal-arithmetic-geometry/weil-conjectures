## What changed

The existing signature of `AlgebraicGeometry.gradedFinitenessCohomology` is byte for byte
unchanged. Its proof obtains the homogeneous action and applies finiteness to that same action.
The added modules are `Sheaf.Paper.GradedCohomologyModuleStructure` and
`Sheaf.Paper.GradedCohomologyModuleFinite`, imported privately by the item's module.
The original public imports are unchanged.

The second reader removed unnecessary Noetherianity, algebra finite type, properness,
quasi-coherence and local generation hypotheses from the NEW action helper. It now isolates
only the algebraic construction, independently of geometric finiteness. The finiteness helper
requires the homogeneous compatibility formula on the very `mod` whose finiteness it asserts.
No existing statement or definition was changed; no change record is needed.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.gradedFinitenessCohomology` (node
`lem-weil-pbc-graded-finiteness-cohomology`). Its proof term combines two open results; this is
NOT an axiom-free proof of the target.

Added holes:

- `AlgebraicGeometry.gradedCohomologyModuleStructure` (node
  `lem-weil-pbc-graded-cohomology-module-structure`).
- `AlgebraicGeometry.gradedCohomologyModuleFinite` (node
  `lem-weil-pbc-graded-cohomology-module-finite`).

There are no holes left in the item's module, and exactly these two named theorem holes in
the new modules. Both have a source, a complete proof in words, and matching DAG records.
This is a DECOMPOSITION: one upper hole closed, two lower holes added, nominal net -1 in
these declarations. It is not claimed as positive ledger progress. Only the pinned-baseline
sorry ledger can determine closure-wide progress; no closure module pruning is claimed.

All three files compile without warnings. Explicit `#print axioms` in scratch copies reports
only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for all three declarations.
No new definitions, chosen objects, axioms, unsafe/opaque declarations or foreign hooks occur.

## No longer needed

Removed the following DIRECT imports from the item's module:

- `Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`
- `Sheaf.AlgebraicGeometry.AffineModuleFiniteType`
- `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`
- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`
- `Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum`
- `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`

These modules are retained as private proof-plan imports by the still-open finiteness helper;
none is claimed pruned from the targets' import closure. The action helper needs none of them.
The new finiteness helper publicly imports Mathlib's quasi-coherent sheaf module for its
quasi-coherence hypothesis; the project's coherent-module definition is only used by its
private geometric proof dependencies. The action helper retains only DirectSum.Module and
PQFCohomology as public statement imports.

Every original DIRECT proof dependency of the item's node is now replaced by the two
helper nodes. For completeness, all removed direct edges are:

- `lem-weil-pbc-proper-fp-permanence`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `def-weil-proper-morphism`
- `lem-weil-pbc-finite-type-over-noetherian`
- `pqf-def-coherent`
- `def-weil-pbc-finite-type-algebra`
- `def-weil-sheaf-of-modules-category`
- `lem-weil-pbc-relative-spec-base-change`
- `lem-weil-pbc-affine-morphism-relative-spec`
- `lem-weil-pbc-affine-module-correspondence`
- `lem-weil-pbc-affine-module-finite-type`
- `pqf-lem-coherent-ft-locnoeth`
- `lem-pc-coherent-hi`
- `lem-weil-pbc-affine-morphism-cohomology-edge`
- `def-weil-pbc-module-cohomology-fmap`
- `lem-weil-pbc-qcqs-cohomology-direct-sum`
- `pqf-def-cohomology`
- `def-weil-finitely-generated-module`

All of these old nodes remain in the finiteness helper's plan; the cohomology and module
category nodes also appear in the action helper's plan. Thus this is relocation of direct
proof dependencies, not global pruning. Globally pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The first report called the upper theorem proved without identifying the decomposition or
its two added holes. Both helper docstrings omitted the proof in words. Both new nodes had
empty proof and search fields and no statement dependencies. The finiteness node additionally
recorded an OLD, different statement: existence of one compatible action supposedly implied
finiteness for EVERY action, with no compatibility required of that action. That is not what
the Lean theorem states and cannot be justified by this argument. Its record now requires
compatibility of the specified action. The item's proof record still had the five original
steps instead of the actual two-helper reduction. These defects were repaired.

The new helper statements are strictly parts of the argument: the first constructs an action
without any finiteness or properness hypotheses and proves no finite generation; the second
assumes the action and proves only its finiteness, following the original geometric plan.
Neither restates the target's existential conjunction. A full proof of either helper was not
available from a directly matching library declaration during the review.

## New nodes

`lem-weil-pbc-graded-cohomology-module-structure` records the extension of homogeneous
cohomology operators to a module action by finite convolution. Its Lean signature, natural
statement and proof agree. The homogeneous formula determines the action uniquely, since B
and the direct sum are additively generated by their homogeneous elements. No arbitrary
witness is used to define data; the target merely eliminates the existential inside a proof.

`lem-weil-pbc-graded-cohomology-module-finite` records geometric finite generation for a
supplied action satisfying that homogeneous formula. It preserves the original relative-spec,
affine-correspondence, coherent-proper-cohomology and qcqs-direct-sum route. The comparison
maps are B-linear because their squares commute on homogeneous maps, then on finite sums.
Both nodes have full stepwise proofs, the same chapter/unit and blueprint ancestor as the
item, new-module Lean records and actual recorded Mathlib searches. No change records.

## Second reading by N3

1. Compared the delivered item with the repository using `diff`, then compared the entire
   existing theorem signature up to `:= by` byte for byte. Verdict: identical. Only its
   proof and private imports change; no existing definitions or statements change. Each new
   helper file is absent from the repository and introduces only its named theorem.
2. Compiled all three modules in import order with `lcompile.py --all`, and compiled scratch
   copies with explicit `#print axioms` for all three declarations. Verdict: no errors or
   warnings; the four axioms listed above only. The two remaining sorries occur exactly as
   whole named theorem proofs, not inside data or partial proofs. Source scans found no
   prohibited declarations or hooks.
3. Read the complete helper signatures and Stacks 0897(1)
   (https://stacks.math.columbia.edu/tag/0897). Checked the action on the zero element, the
   scalar 1 in degree zero, empty X, the zero family, p=0, and the grading concentrated in
   degree zero. All are consistent: empty X/zero family give the unique zero action and a
   finite zero module; the degree-zero case reduces to ordinary algebra action and proper
   coherent finiteness. The finiteness argument uses quasi-coherence for affine localization,
   hfinite for finite generation, Noetherianity for coherence, and properness for cohomology
   finiteness, with no hidden ampleness or flatness assumption. An arbitrary supplied action
   is NOT allowed without its compatibility formula. Verdict: the repaired nodes are true,
   sufficient and strictly smaller than the target. Added full proof docstrings.
   Independent searches used leanfinder (homogeneous additive-map extension and relative-spec
   cohomology finite generation), loogle (`DirectSum.IsInternal, Module`), and grep for
   `moduleCohomology|gradedCohomology|coherent.*cohomology` in Mathlib/AlgebraicGeometry.
   LeanSearch was attempted and returned Internal Server Error; its unavailability is
   recorded without a no-match verdict. Loogle and LeanFinder found generic graded module
   infrastructure, notably DirectSum.Gmodule; this does not by itself instantiate the
   cohomology maps or degree transports. Read GradedModule.lean to check that distinction.
   Searched lean/Sheaf, lean/WeilConjectures and the source checkout for graded cohomology:
   no identical helper; existing affine and proper finiteness results are retained as proof
   dependencies. No quick complete proof of a helper was found.
4. Read the original five-step proof and its dependency node statements. The target now
   takes the short conjunction route through action construction and finiteness for that
   action; the geometric route remains in the second helper. Read
   `dag/units/sk-thm-p1.json`: neither this item nor its old direct dependencies realizes a
   unit statement or step. No realized node or unit route is bypassed. Verdict: route kept;
   unused direct imports removed and every removed direct DAG edge listed above; no global
   module pruning asserted.
5. Checked Lean declarations against all three nodes. Replaced the stale finiteness signature
   (which was not the actual Lean statement), added self-contained statements, statement
   dependencies, nonempty stepwise proofs, their union as proof_deps, source origins and
   three search kinds to both new nodes. Updated the existing node to the actual two-step
   reduction. Verdict: records agree with Lean and no changes outside the existing node's
   stage-3-owned fields are requested.

Changes from this second reading: removed redundant action-helper hypotheses and imports;
removed the item's redundant direct proof imports; supplied complete proof docstrings;
fixed line-length warnings; corrected and completed new-node records and the item's proof
record; clarified decomposition, hole counts and pruning in this report.
