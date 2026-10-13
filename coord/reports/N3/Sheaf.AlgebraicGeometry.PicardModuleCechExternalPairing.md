## What changed
Proved `AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalPairing` without changing
its signature. Added the proved module `Sheaf.AlgebraicGeometry.PicardExternalCechModuleRepresentatives`
to transport scalar Cech cycles to ordinary module cycles and identify the external pairing
with the ordinary front/back cup cochain. Its private helpers prove cycle-map and homology
transport formulas from Mathlib naturality and the existing explicit additive Cech isomorphisms.

The item's proof constructs the product cover and both prescribed refinements, establishes
quasi-coherence of the pulled-back coefficients by uniqueness of left adjoints and the source
library's pullback theorem, obtains the two canonical comparisons, and applies the existing
Cech resolution cup representatives and the two refinement comparison squares. The final
step evaluates morphism equalities with `AddCommGrpCat.comp_apply`; local irreducibility keeps
Lean from expanding resolution-based cohomology pullback definitions during elaboration.

Proof-only imports added: the new representatives module, `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`,
`Sheaf.Paper.CechComparisonMapNaturality`, `Sheaf.Paper.CechRefinementComparisonSquare`,
and `Sheaf.Paper.CechCupResolutionRepresentatives`. Existing public imports and the statement
are preserved. Both DAG proofs record the implemented route. No existing definition or statement was weakened, and no other module was adapted.
The dry-run tool refreshed to a baseline where the assigned module and its original
node are absent. The delivery therefore restores that module with exactly the signature
read at the start of the task, and records both nodes as additions on the refreshed baseline.
The restoration is documented in `coord/changes/picard-module-cech-external-pairing-restore.md`.

## Proved and sorry left
Closed the one original hole in the module provided by the brief: `AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalPairing`
(node `lem-sc-picard-module-cech-external-pairing`).
Also proved the new `AlgebraicGeometry.Scheme.Modules.picardExternalCech_moduleRepresentatives`
(node `lem-sc-picard-external-cech-module-representatives`).
The refreshed baseline lacks the assigned module, so no decrease of its current
closure ledger is claimed; that ledger is the maintainer's check.
No holes were added or remain in the delivered modules, and no intermediate statement is left
for another worker. The proofs use the existing library's named comparison and resolution
theorems, whose remaining dependency holes are not claimed closed by this delivery.

## No longer needed
Removed the proof import `Sheaf.Paper.CechCupPullbackCompat` and the direct parent dependency
`lem-sc-picard-cech-cup-pullback-compat`: its coefficient, composition, pullback, and cup
naturality package is not used. The proof uses its existing constituent refinement square
and Cech resolution representatives directly. The original Cech cup product, prescribed
refinement map, and bidegree coordinate nodes remain needed via the new representatives node.
No other original node or module is claimed unnecessary. The unit record has no realized
statement or step at this node, and the unit's cube-theorem route is preserved.

## Where the brief, the DAG or earlier work was wrong
The earlier sandbox report identified the missing scalar-cycle transport interface but left
the original hole unchanged. This attempt supplies and proves that interface explicitly;
there is no mathematical obstruction or changed hypothesis. The planned argument can use
the existing refinement square and resolution representatives directly rather than import
the entire cup-pullback compatibility module. The refreshed delivery baseline removed
the assigned module/node during the work, requiring restoration metadata and a change
record. The original theorem signature is preserved verbatim. Degree zero, empty index families, and zero
coefficients are covered by the same coordinate and cycle-map calculations; no affine or
comparison-isomorphism assumptions were added.

## New nodes
`lem-sc-picard-external-cech-module-representatives` records the proved Cech-only transport
and cochain cup identity. It has no module cohomology comparisons or covering hypothesis,
and is strictly the cycle-and-coordinate part of the parent's argument. Its construction
uses explicit cycle maps and an explicit additive Cech complex isomorphism, not an arbitrary
witness selected from an unproved existence theorem.

`lem-sc-picard-module-cech-external-pairing` is restored because it is absent on the
refreshed delivery baseline. It retains the statement supplied by the brief, with the
proved route above. Change record: `coord/changes/picard-module-cech-external-pairing-restore.md`.

## Second reading by N3

1. Interface preservation: the repository version of the assigned module is absent,
so a direct `diff` reports a missing baseline file, as the restoration record states.
Both delivered theorem signatures match their node's `lean.statement` byte for byte;
the assigned theorem also matches the verbatim signature in the restoration change
record. No existing repository module is adapted. This verifies consistency of the
restoration, but the absent historical source prevents an independent byte comparison
with the original assigned source. The restoration remains an interface addition for
independent delivery review, with no assertion of current closure-ledger improvement.

2. Proof check: compiled both delivered modules in import order with `lcompile.py`:
59.0 seconds for the representatives module and 38.9 seconds for the assigned module,
without errors or warnings. Scanned both complete sources: no `sorry`, `axiom`,
`unsafe`, `opaque`, `implemented_by`, or `extern`; no line exceeds 100 characters.
The private cycle constructions use explicit functorial cycle maps and the explicit
Cech isomorphism. Choices of comparisons and resolution representatives occur only
inside theorem proofs; no definition chooses arbitrary data from an unproved
existence statement. The axiom checks and delivery preflight are recorded below.

3. New statement check: there are no split-off holes. The proved representatives
lemma is strictly the cycle-and-coordinate portion of the argument: it has no
covering condition or derived-cohomology comparison. Checked the definitions of
IsPicardExternalCechCupBidegree and IsCechRefinementMap against the final restriction
calculation. Degree zero uses the same one-vertex front/back faces; an empty index
family has no tuples, and zero coefficients give zero sections, so the construction
and equations still apply. Independent searches used the query “homology class of
cycles transported along an isomorphism of cochain complexes after forgetting module
scalars” (LeanFinder), `ShortComplex.mapCyclesIso, ShortComplex.homologyπ` (Loogle:
identifier unavailable, not an absence verdict), and
`cyclesMap.*homologyπ|mapHomologyIso.*homologyπ` (Mathlib grep). Grep found the
naturality lemmas already used. Local source searches found related private
map-homology-projection helpers in ShortComplexSectionComparison and
CechComparisonInverseImageCompatibility, but no accessible replacement for the
new public external-pairing representatives theorem.

4. Route and pruning: read the proof from the assigned theorem through the new
representatives theorem and its private transport helpers. The direct coordinate
calculation followed by the existing resolution-representatives theorem and the two
refinement squares proves precisely the stated comparison, without affine-cover or
invertibility assumptions. All public imports provide names in the statements;
added proof imports are plain imports. The report identifies the removed
CechCupPullbackCompat import and its node; its constituents remain needed. Since the
old source/node are absent, completeness of the historical dependency difference
can only be checked against the first reader's recorded baseline. The unit
`sk-prop-av-cube` has empty realized statement/step lists, and this local reduction
changes neither its statement nor its cube-theorem route.

5. DAG check: both signatures match Lean byte for byte; every proof/statement
dependency names an existing node or the new representatives node. In each node,
`proof_deps` is exactly the union of the proof steps' `uses`. Read the referenced
pullback quasi-coherence, refinement, comparison-naturality and resolution statements;
the recorded proof steps and proof origins agree with their use in Lean. The new node
has its source, searches, creation, blueprint, chapter, unit and Lean fields. The
restored node and change record accurately identify the baseline absence.

Changes by the second reader: appended this review and independent verification
results. No Lean proof, signature, definition, import or DAG node needed repair.

Axiom verification: scratch copies with `#print axioms` compiled successfully.
`picardExternalCech_moduleRepresentatives` uses exactly `propext`,
`Classical.choice`, and `Quot.sound`. `picardModuleCech_externalPairing` additionally
uses `sorryAx` through existing imported results; in particular, the existing
`cechCup_resolution_representatives` is still open in the repository. This delivery
closes the assigned local hole, not those imported dependency holes. Scratch copies
were removed before delivery.

Delivery validation: `deliver3.py N3 Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing
--no-push` printed OK: both modules compiled and preflight passed. Review class CODEX
reflects the restored module, the proved helper module, added nodes and restoration
change record; no imported dependency hole is claimed closed.
