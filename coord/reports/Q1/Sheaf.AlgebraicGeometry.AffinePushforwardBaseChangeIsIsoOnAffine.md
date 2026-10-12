## What changed

Added `Sheaf.AlgebraicGeometry.AffineBaseChangeChartCoordinates`, stating only the
compatible-affine-chart coordinate calculation. The item now combines that calculation
with a proved tensor reassociation and Mathlib's sheaf isomorphism criterion on a basis.
Its existing public theorem signature and public imports are unchanged. New imports used
only by proofs are ordinary `import`, including `AffineBaseChangeTensorComparisons` in
the chart module. No existing definitions or statements changed; no change record is needed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.affinePushforward_baseChange_app_bijective`
(node `lem-weil-pbc-affine-pushforward-base-change-app-bijective`), one of the item's one
original holes. The private helper `tensor_baseChange_equiv` is proved without sorry.

Hole added and left: `AlgebraicGeometry.Scheme.Modules.exists_affineBaseChange_chart_coordinates`
(node `lem-weil-pbc-affine-base-change-chart-coordinates`), in its own new module.
No other holes were added. This is a decomposition: one upper hole closed, one smaller
hole added, net zero, not a completed axiom-clean proof of the item. The axiom check of
the public item still includes `sorryAx`; the new chart theorem includes `sorryAx`.
The tensor helper uses only the permitted standard axioms.

## No longer needed

Removed the proof-only import `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`.
The old item node had empty `proof_deps`, so no old proof-dependency node was removed.
The new proof uses only `lem-weil-pbc-affine-base-change-chart-coordinates` as a DAG proof
dependency. No claim is made that LocallyFreeAffine is globally unreachable from targets;
its import is pruned from this item. No unit node or unit-level route is removed.

## Where the brief, the DAG or earlier work was wrong

The old item node had no proof dependencies. The local geometry needed by its affine
computation is now named rather than left inside an unfinished proof. The first worker's
chart module omitted the ordinary proof import of `AffineBaseChangeTensorComparisons`,
although its docstring and node planned to use it. The old report did not distinguish
one-hole decomposition from net progress. Its import change record was unnecessary:
all changed imports are proof-only. The second reader removed that record. The first
dry run also classified the added `open TensorProduct` as an interface change. Rather
than changing global namespace commands, the item now uses fully qualified tensor
types and constructors; its namespace commands are identical to the original.

## New nodes

`lem-weil-pbc-affine-base-change-chart-coordinates`, at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-base-change-chart-coordinates.json`,
states the actual linear coordinate formula on compatible affine charts. It does not
state global bijectivity and does not assume the item. Its module has a named theorem
with a complete natural-language proof, source tags, and blueprint tag. No change record.

## Second reading by Q1

1. Compared the item's entire module with the repository using `diff`. The sole existing
   public declaration's signature is byte for byte unchanged (also checked by extracting
   the text before `:= by`). No existing definition changed, no hypothesis was added,
   and no conclusion was weakened. The new tensor helper is private. Public imports of
   the existing module are unchanged; the removed LocallyFreeAffine import was private.
   Verdict: unchanged interface.
2. Compiled both delivered modules in import order through `lcompile.py --all`. Reviewed
   the tensor equivalence: commutation, cancellation of base extension, tensor congruence
   with commRight, and final commutation give precisely the pure-tensor formula; simp
   checks it. Tensor induction proves equality of the coordinate map and equivalence.
   Injectivity and surjectivity are then transported through a and b. A basis of opens
   subordinate to affine inverse images is constructed explicitly, and the additive
   sheaf criterion gives bijectivity on all opens. No forbidden declaration or hollow
   definition occurs. A scratch copy with `#print axioms` checks both public theorems
   and the private helper; the public proofs may use only standard axioms and sorryAx
   from open statements. The new chart theorem is the sole delivered sorry.
   Verdict: genuine reduction, with its remaining hole explicitly recorded.
3. Read Stacks Project [02KG](https://stacks.math.columbia.edu/tag/02KG) and
   [01I9](https://stacks.math.columbia.edu/tag/01I9), since the literature checkout is
   absent here. Their hypotheses are an affine f and quasi-coherent F; arbitrary base
   change is allowed. Read the full existing `exists_affineBaseChange_tensorComparisons`
   theorem and `moduleBaseChangeMap_open_restriction`. The former gives unit-normalized
   tensor coordinates on spectra; the latter identifies the map on full inverse-image
   open squares. The chart lemma supplies the remaining affine-chart identifications
   and canonical-map formula, while reassociation and passage from a basis to all opens
   are separately proved in the item. It is a strictly local part of the argument,
   rather than the item under another name. Tested in words: empty U forces empty W
   and zero section modules; empty W and F = 0 also give zero tensors; identity f or g
   reduces to the ordinary unit/localization tensor comparison. No nonzero-ring,
   nonempty-chart, flatness or separatedness assumption is needed. Independent searches
   used LeanFinder's quasi-coherent pushforward query, Loogle, and grep with
   `tensorPullback|pushforwardSpecMapCompΓIso|isIso_iff_isIso_basis`, plus rg in Mathlib,
   upstream modules and lean/Sheaf. No exact existing chart lemma was found. Existing
   `affinePushforward_baseChange_affine_formula` is a spectra-only downstream theorem
   importing this item, so importing it would be circular. The tensor-comparison
   theorem is usable and is now privately imported. Verdict: true, needed local split.
4. Checked the shortest available route: the item already uses Mathlib's tensor
   cancellation and sheaf-basis criterion, while the geometric coordinate step remains
   unproved. Removed unused LocallyFreeAffine; kept imports required by signatures and
   proof steps. Read `dag/units/sk-thm-p1.json` and its realized statement/steps: neither
   this item nor the new chart lemma replaces a realized unit statement or step, and
   the curve/strict-henselian/stalk route is untouched. Verdict: below-unit reduction
   and complete pruning report for the old empty proof_deps.
5. Read both delivered nodes and compared the old item node. The item's proof_deps is
   exactly its one used chart node. Its proof now names the actual Mathlib operations
   and removes the spurious chart-node citation from the basis step. The new node has
   its own module, verbatim Lean signature, self-contained statement with all four
   rings/modules defined, source, searches, creation record, unit/chapter and blueprint
   origin. Its planned dependencies are the tensor comparisons and open-restriction
   theorem, with the module-base-change definition also recorded in stmt_deps.
   Verdict: nodes agree with the completed upper proof and documented lower plan.

Second reading changed: added the missing proof-only tensor-comparison import and module
blueprint tag; expanded the chart docstring's adjunction-unit calculation; made the new
node statement self-contained and recorded its statement dependency; clarified Mathlib
steps and removed a spurious dependency use in the item node; rewrote the report to
record decomposition and precise pruning; removed the unnecessary import change record;
qualified tensor syntax in the item to retain the original namespace commands.
