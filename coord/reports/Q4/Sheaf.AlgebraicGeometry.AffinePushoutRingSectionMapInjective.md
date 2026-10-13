## What changed

Replaced `AlgebraicGeometry.Scheme.Modules.affinePushoutSectionMap_injective`'s
sorry with the stated affine-module route. Prove quasi-coherence of the pushforward
regular module, apply the affine section comparison, compose with the regular-module
comparison and tensor swap, identify the result with the constructed ring map by
its pure-tensor formula and tensor induction, then cancel three injective maps.
All added imports in the existing module are private proof imports. The existing
signature and docstring are unchanged.

The general sheaf-level regular-module comparison was not stated in the library.
It is isolated in `Sheaf.AlgebraicGeometry.PushoutRegularModuleComparison`, with
one named theorem and a DAG node. Its statement has no affine-open or affine-morphism
hypothesis and no tensor section injectivity conclusion, so it is strictly the
sheaf-identification step, not a restatement of the assigned theorem.

## Proved and sorry left

Closed the one upper hole:
`AlgebraicGeometry.Scheme.Modules.affinePushoutSectionMap_injective`
(node `stage3-affine-pushout-ring-section-map-injective`).

Added one lower hole:
`AlgebraicGeometry.Scheme.Modules.exists_pushout_regularModule_comparison`
(node `stage3-pushout-regular-module-comparison`). Its proof is exactly `by sorry`.
There are no other added holes and no sorry inside a definition. This delivery
is a decomposition (one hole closed, one added), not a net sorry reduction.
The comparison uses neither affineness nor the affine section theorem. Its
regular-module tensor inverse formulas apply also to the zero ring and empty open.

## No longer needed

None. No existing import was removed. The original cancellation dependency
`lem-weil-pbc-affine-module-tensor-base-change` is now below the new regular-module
node, rather than a direct dependency of the assigned module. It remains needed;
no unit route, node, or module is claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The original step 2 needed a regular-module identification with its unit formula
that no existing public theorem states. `AffineModuleTensorAlgebraQuasiCoherent`
contains private `inverseImage_unit_iso` and `changeOfRings_unit_iso` helpers,
but their conclusions provide only isomorphism existence and no unit formula.
They cannot supply the comparison required in this module. The new node states
exactly that step. The remaining affine-section argument is implemented rather
than postponed.

The compiled snapshot initially lacked `AffinePushoutRingSectionMap.olean` and
`AffinePushoutRingSectionDelta.olean`. Even the original assigned module failed
its initial compile for that reason. A temporary prototype of the combining
argument, parameterized by a ring map with the stated pure-tensor formula,
compiled against available dependencies. No repository dependency was copied,
redefined, or edited to work around this missing snapshot.

## New nodes

`stage3-pushout-regular-module-comparison`, in
`dag/nodes/sec-proper-base-change/stage3-pushout-regular-module-comparison.json`,
is the regular-module specialization of the existing ring-sheaf pushout
cancellation comparison. It retains the source route of Stacks Tags
[01SB](https://stacks.math.columbia.edu/tag/01SB) and
[008A](https://stacks.math.columbia.edu/tag/008A), read directly because this
machine has no local Stacks source files. Its docstring and node give the
inverse-image regular-module identification, the balanced tensor inverse maps,
and the canonical unit calculation. No change record is needed: no existing
interface changes.

Validation status: both actual delivery modules compile against the refreshed snapshot
(`PushoutRegularModuleComparison`: 3.4 seconds;
`AffinePushoutRingSectionMapInjective`: 9.4 seconds). The missing dependency
artifacts from the previous attempt are now available. Removing the private
`Mathlib.AlgebraicGeometry.Morphisms.Separated` import caused an unknown-identifier
error for `IsSeparated.of_isAffineHom`, so that necessary proof import is retained.
`deliver3.py --no-push` printed OK: compilation and preflight passed, except for
the second-reading section which the second reader writes. Nothing was pushed.

The first current dry run passed local compilation and the axiom probes, then
failed at fetching the delivery base because the server connection timed out.
The retry succeeded. This transient network failure is separate from the repaired
snapshot issue.

## Second reading by Q4

1. Interface: PASS. Diffed the assigned module against the repository version.
   Its existing declaration signature and docstring are byte-for-byte unchanged;
   only private proof imports, local elaboration options and the proof changed.
   The other delivered module is new. There are no changed definitions or
   undeclared interface changes, and no change record is required.
2. Proof and trust: PASS as a decomposition. Compiled both delivered modules in
   import order with lcompile.py (3.0 and 8.6 seconds), without warnings or errors.
   Scratch copies with explicit #print axioms for both public declarations showed
   exactly propext, Classical.choice, Quot.sound and sorryAx. The assigned theorem
   has no local sorry; the sole added hole is the named regular-module comparison.
   No axiom, unsafe, opaque, implemented_by, extern, or holed definition occurs.
   The existential comparison is destructured inside a theorem proof; it is not
   used to define arbitrary data from an unproved existence statement.
3. Split statement: PASS. Read the complete comparison, its docstring, its node,
   tensor-pullback adjunction and affine-module cancellation theorem. The adjunction
   witness is pinned by its unit formula. The regular inverse-image identification
   and scalar-extension maps z tensor a ↦ z*t(a), z ↦ z tensor 1 give the claimed
   comparison and formula. For f = identity it specializes to scalar extension
   along an isomorphism; for an empty open or zero target algebra the same maps
   act on zero modules. No flatness, affineness, or nonempty assumption is hidden.
   It is a sheaf-identification step, not a tensor-section injectivity restatement.
   Independently repeated Loogle, LeanFinder and grep searches with rank-one/free
   module and pullback-unit terminology, plus rg across both Lean roots. Inspected
   Mathlib Sheaf/PullbackFree.lean: pullbackObjUnitToUnit handles the unit module
   itself, not the restricted regular algebra module in this pushout, so does not
   replace this theorem. The existing private inverseImage_unit_iso and
   changeOfRings_unit_iso helpers do not state the required unit formula.
   Re-read [Stacks 01SB](https://stacks.math.columbia.edu/tag/01SB) and
   [Stacks 008A](https://stacks.math.columbia.edu/tag/008A): the new comparison is
   the expanded scalar-extension step of the recorded source route. Formalizing
   its inverse-image and sheafification compatibilities is not a few-minute closure.
4. Route and pruning: PASS. Read the affine section comparison and traced the
   tensor swap, pure-tensor calculation, additive induction and three injectivity
   cancellations. Every added private import supplies a used declaration, including
   the upstream quasi-coherence-of-unit instance and separatedness instance.
   Both public imports in the new module are needed by its signature. Of the old
   proof_deps, only lem-weil-pbc-affine-module-tensor-base-change ceased to be a
   direct use; it remains a dependency of the new comparison, as already reported
   under No longer needed. All other old dependencies remain direct uses. No
   module is pruned. Read dag/units/sk-thm-p1.json and its realized route: no unit
   statement or step is replaced or bypassed; this is a split below the unit level.
5. DAG: PASS. The updated item's proof steps, proof_deps and proof_origin match
   quasi-coherent pushforward, the new comparison, affine sections and the tensor
   formula used in Lean. The new node has a self-contained statement, source,
   full proof steps and their dependency union, independent search records,
   creation and blueprint provenance, chapter/unit, split status and matching
   Lean declaration record. Existing node interface fields are unchanged.

Changes by the second reader: added this independent review and search evidence
only. No Lean or DAG repair was necessary. One original hole is closed and one
strictly lower hole is added; net hole reduction is zero, with no pruning.
