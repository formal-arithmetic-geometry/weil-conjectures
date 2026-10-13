## What changed

Replaced the sorry in `AlgebraicGeometry.singleComplexOpen_coordinates_transport`
without changing its signature, existing docstring, or public imports. Its proof
uses the already proved `SingleComplexBaseChange.nonempty_coordinates` to obtain
coordinates for the constructed restricted coefficient. It then transports
invertibility in both directions through an additive-arrow isomorphism, using
Mathlib's `Arrow.isIso_iff_isIso_of_isIso` and the module forgetful functors'
reflection of isomorphisms.

Added one proof-only import and one new module,
`Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkEquivalence`. The new
statement isolates the stalk-conjugacy calculation: it takes restricted
coordinates as input and asserts an isomorphism of additive arrows. It does not
choose coordinates and does not assert the original existential invertibility
statement. The target's coordinate existence and both invertibility directions
are complete Lean proofs. The two DAG records describe this route.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.singleComplexOpen_coordinates_transport`
(node `lem-pc-single-complex-open-coordinate-transport`).

Added one hole in
`AlgebraicGeometry.nonempty_singleComplexOpen_stalk_arrow_iso`
(node `lem-pc-single-complex-open-coordinate-stalk-equivalence`), in the new
module `SingleComplexOpenCoordinateStalkEquivalence`. Its theorem proof is
exactly `:= by sorry`, with its source and the complete intended argument in
its declaration docstring. There are no remaining sorries in the item module
and no other added holes. This is a decomposition (one hole closed, one added;
net zero), not a claim that the stalk calculation has been proved.

Both delivered modules compile together without warnings. No definition,
existing signature, universe, binder, or visibility was changed. No data
construction was added; coordinate and arrow witnesses are eliminated only
inside the proof of the proposition.

## No longer needed

Second reading removed the redundant public import
`Mathlib.AlgebraicGeometry.Restrict` from the new stalk-equivalence module;
`SingleComplexOpenRestrictionData` already publicly imports it.

No existing import was removed: the item's three public imports support its
unchanged statement and remain visible to importers. There were no existing
proof-only imports to prune.

The special construction of a restricted coordinate presentation in the original
node's first step is unnecessary: `nonempty_coordinates` supplies coordinates
for the canonical restricted coefficient. In particular this route does not use
`lem-pc-kflat-open-restriction` / `Sheaf.AlgebraicGeometry.Modules.IsKFlatRestriction`.
The new stalk lemma compares arbitrary representatives via exact derived stalks
and ring isomorphisms instead of constructing termwise restricted coordinates.
K-flatness at stalks is used through `lem-pc-kflat-stalk-criterion`.

The other former proof dependencies remain necessary in the lower stalk lemma
or in the statement's definitions: `def-pc-derived-open-restriction-maps`,
`lem-pc-ringed-spaces-derived-pullback-composition`,
`def-pc-single-complex-base-change-stalk-condition`,
`def-pc-single-complex-open-restriction-data`,
`lem-pc-open-restriction-stalk-extension-iso`, and
`def-pc-base-derived-tensor-cohomology-model`.
No claim is made that a module used elsewhere in the targets' closure becomes
unreachable. The source-open `SingleComplexOpenStalkConjugacy` lemma is not
imported: it keeps S and S' fixed and does not state this target-open comparison.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The original DAG called for
constructing a particular restricted presentation, although the statement only
requires existence of some presentation. Existing coordinate existence allows
this step to be discharged independently of the original coordinates.

The hard remaining calculation changes all four local rings and compares the
pinned localized tensor maps. Same-square coordinate invariance and the
source-open pullback conjugacy statement do not by themselves state it. It is
isolated as the new additive-arrow lemma, with an explicit natural-language
argument explaining local-ring transport, tensor-algebra linearity, coefficient
normalization, and the counit factorization. This is below the unit level;
`dag/units/sk-thm-picard-semicon.json` records neither this node nor a proof step
as a realized unit statement/step. The surrounding target-locality route stays.

Searched LeanFinder, Loogle, LeanSearch and Mathlib/library sources. LeanFinder
found the Arrow isomorphism lemmas used for the final glue, and restriction
section-map formulas, but no scheme target-open conjugacy theorem. Loogle found
stalk-map and restriction-stalk formulas; an earlier Arrow query was rate-limited.
LeanSearch returned Internal Server Error, recorded as unavailable. Local search
found `StalkComparisonCoordinateInvariance` and `SingleComplexOpenStalkConjugacy`,
whose signatures cover different cases. Search details are in the new node.

Read Stacks Tags 0DJ9 and 0DJ8, the equation-bc setting, and Tags 08HY and 08FE
from the Stacks website because the local non-git literature was absent. The new
lemma expands the stalk-local calculation rather than quoting a new general
isomorphism theorem from these sources. Its proof origin is recorded as agent.

Edge cases checked for the new statement: empty U' has no point z; top opens
use the same stalk isomorphisms; zero rings and zero complexes are allowed by
scalar-equivalence and homology functoriality; arbitrary unbounded complexes
remain in scope. No flatness over the base stalk, quasi-coherence, boundedness,
affineness, or original stalk condition is assumed.

## New nodes

`lem-pc-single-complex-open-coordinate-stalk-equivalence`, in
`dag/nodes/sec-picard-framework/`, records
`AlgebraicGeometry.nonempty_singleComplexOpen_stalk_arrow_iso` in
`lean/Sheaf/AlgebraicGeometry/SingleComplexOpenCoordinateStalkEquivalence.lean`.
It is the comparison-arrow conjugacy subargument for given original and
restricted coordinates; the target proof separately obtains restricted
coordinates and derives the module invertibility equivalence. There are no
change records or forced adaptations.

## Second reading by N3

1. **Interface preservation: pass.** Diffed the delivered item against the repository.
   The sole existing declaration, `singleComplexOpen_coordinates_transport`, has
   the identical signature, universes, binders, let-bound coefficient, docstring,
   and visibility. The changes are its proof and a plain proof-only import. The
   new module adds a theorem, with no definitions or interface adaptations.
2. **Proof and holes: pass, as a decomposition.** Independently compiled both
   modules in import order. The existential coordinates come from the proved
   `nonempty_coordinates`; the arrow isomorphism is eliminated within Prop.
   `Arrow.isIso_iff_isIso_of_isIso` and the two scalar-forgetting functors give
   both directions with the correct orientation. There is exactly one added
   sorry, the named `nonempty_singleComplexOpen_stalk_arrow_iso`; no forbidden
   declaration or data choice was added. A scratch axiom check is recorded below.
3. **Split lemma: pass.** Read its full signature, proof docstring, and node against
   [Stacks 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9),
   [0DJ8](https://stacks.math.columbia.edu/tag/0DJ8),
   [08HY](https://stacks.math.columbia.edu/tag/08HY), and
   [08FE](https://stacks.math.columbia.edu/tag/08FE). These motivate the calculation;
   they do not state this exact coordinate-arrow lemma. The claimed argument is
   a local calculation and uses no quasi-coherence, qcqs, affine, boundedness,
   or base-flatness hypothesis. At a point, all four open stalk maps are ring
   isomorphisms; hj fixes the point in X, and the restriction squares fix its
   images in S and S'. Transporting these ring maps identifies the tensor algebra
   and C-action. Exact derived stalks of e and e' identify the representatives;
   counit-compatible derived tensor transport identifies the sources. The
   represents equations identify the coefficient maps after target normalization,
   and the defined restricted coefficient uses those same pinned composition
   and open-pullback comparisons. Thus the arrows are conjugate, rather than
   being assumed invertible. Empty opens have no z; top opens use the same stalk
   maps; zero complexes have zero homology; degree-zero and unbounded complexes
   use exactly the same functorial cohomology identities. No additional coordinate
   witness is chosen by the new theorem. It isolates the original second step
   for given coordinates: coordinate existence and invertibility reflection are
   proved separately in the item. It is not an existential restatement.

   Independently searched LeanFinder for restriction of base schemes preserving
   derived tensor stalk comparison, Loogle for resLEStalkMap, and rg for stalk
   restriction and coordinate transport in lean/Sheaf, lean/WeilConjectures and
   the upstream AlgebraicGeometry tree. The Mathlib results resLEStalkMap,
   morphismRestrictStalkMap and restrictStalkNatIso supply local identifications,
   not the derived coefficient comparison. Read StalkComparisonCoordinateInvariance,
   StalkComparisonSourceTransport and StalkComparisonPullbackNaturality: their
   public theorems concern a fixed square; they apply to representative changes
   after ring transport but do not themselves assert cross-ring transport.
   SingleComplexOpenStalkConjugacy fixes S and S', so cannot replace this lemma.
   Completing the remaining calculation requires a substantial formal proof,
   not a short application of any searched declaration.
4. **Route and pruning: pass.** Checked the old proof_deps against the report.
   All seven old dependencies are accounted for: kflat-open-restriction is
   bypassed; the other six remain used as definitions or in the lower calculation.
   For the item's direct proof, all old dependencies except
   def-pc-single-complex-base-change-stalk-condition are replaced by the new
   stalk-equivalence dependency; those remaining in the lower calculation are
   transitive, not direct applications in the item. The item retains its original
   public imports to preserve visibility. Removed the new module's redundant
   public Mathlib.AlgebraicGeometry.Restrict import: OpenRestrictionData already
   publicly supplies it. Arrow is needed by the new public statement.
   The unit sk-thm-picard-semicon has realized statement=[] and steps=[[]]; neither
   item is a realized unit step. This reduction stays within the existing
   target-locality/open-restriction route.
5. **DAG agreement: pass.** The item's two steps match coordinate existence and
   arrow/forgetful transport exactly; proof_deps is their union. The new node
   records the one remaining stalk calculation, its source, proof steps, creation,
   blueprint ancestry, searches and verbatim Lean declaration. Its dependencies
   are the intended lower proof, not a claim that the sorry body applies them.
   Neither node depends on the item from below. Corrected the rate-limited Loogle
   search verdict to unavailable rather than no match.

Changes in this reading: removed the redundant public Restrict import in the new
module, added its module-docstring heading marker, corrected the unavailable search
verdict, and clarified direct versus transitive pruning here. No statement or
proof body changed. One original hole is closed and one lower hole added: net zero.

Scratch `#print axioms` checks compiled successfully for both delivered declarations.
Each reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`;
the latter is expected for the documented lower hole and existing open dependencies.
The final delivered files compile together cleanly after the import cleanup.
