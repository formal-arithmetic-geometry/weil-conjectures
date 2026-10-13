## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.DerivedTensorPrecompositionOpen` with
an unchanged-signature proof from existing declarations. Added private, proved categorical
helpers for homology and unit comparison, exact localization transport, local pullback
invertibility, transport of localization existence along an equivalence, and local tensor
invertibility, and reflection through an equivalence. The proof constructs the unit comparison, proves quasi-coherence through the
standard localizations, and uses natural restriction comparisons to prove invertibility of
the displayed composite.

Added proof-only imports of `DerivedPullbackMonoidalModel`, `DerivedPullbackTensorQCoh`,
`DerivedTensorQCohClosure`, `PerfectImpliesQCoh`, `AffineDerivedPullbackTensorTilde`, and the
upstream exact-functor comparison module. Updated the item's DAG proof and proof dependencies
to describe these steps, including perfect quasi-coherence. No public signature, definition,
or public import changed. The unit's route is unchanged.

## Proved and sorry left

Closed `AlgebraicGeometry.exists_derivedTensor_precomposition_open`
(`lem-sc-derived-tensor-precomposition-open`): one of one original holes.
No holes added, none split off, and no `sorry` remains in the delivered module.
This is a proof from the existing stated dependencies; their remaining proofs remain
separate stage-3 items. All new private helpers are proved.

The argument applies without additional geometry assumptions and includes the empty open,
zero tensor factor, and identity map to the unit. The tensor step is natural on arrows,
not merely a comparison of objects. The auxiliary open derived category is obtained from
an actually proved transport of localization existence, not a sorried existence statement.

## No longer needed

No imports removed. All three original public imports are needed for the statement. All six added
proof-only imports are used. The original geometric proof dependencies are retained;
`def-pc-perfect-complex` is no longer a proof dependency; it remains a statement
dependency and its module remains a public import for `Scheme.IsPerfect`. The proof instead
uses the explicit perfect-quasi-coherence theorem `lem-sc-perfect-qcoherent`.
No node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The plan requires perfect implies quasi-coherent but did not list the existing theorem
`lem-sc-perfect-qcoherent` as a proof dependency; added that dependency. The mathematical
statement and proof route need no correction.

The supplied over-site derived categories are not initially derived categories on the
open subschemes. The proof supplies the latter by transporting localization through the
canonical module equivalence in the same universe, then reflects invertibility through
its derived functor. Explicit functor and equivalence types retain the canonical
`SheafOfModules` category instance, avoiding the separately named `Scheme.Modules` instance.

Read the Stacks proofs of Tags 08DW and 08DX and the final paragraph of Lemma 48.4.4
in Tag 0E4G online because the literature sources are not populated on this machine.
The proof uses only the recorded library lemmas and elementary categorical transport;
there are no new nodes or forced adaptations.

Validation: the complete module compiled locally with no holes. The local heartbeat
limit is raised only for the pullback comparison, whose explicit localization choices
require additional definitional-equality reductions. The delivery dry run is the final check.

Preflight compiled the module and completed its axiom check. Its conservative interface
check also flags the file-level proof elaboration commands, despite unchanged signatures
and public imports. The change record is
`coord/changes/derived-tensor-precomposition-open-elaboration.md`; it records the old and
new signature, command scope, and all textual downstream users. The independent reader
can verify that no downstream adaptation or target statement review is needed.

## Second reading by K1

1. **Unchanged interface: PASS.** Compared the complete delivered module with the repository
   using `diff`. The sole existing theorem signature is byte for byte identical, as are
   the public imports and its existing docstring. New helpers are private. The change
   record accurately describes the file-local options, namespace opening and local
   instance attributes; these do not register exported instances or change target data.
2. **Proof and data: PASS.** Independently compiled the whole module with `lcompile.py`
   (35.9 seconds, no errors or warnings). No forbidden declaration or `sorry` occurs.
   An independent scratch-copy `#print axioms` reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` from still-open imported dependencies;
   this closes the local hole and is not a claim of an axiom-clean import closure.
   The unit and homology comparisons are explicit localization constructions. The open
   derived category is transported by a proved universal-property argument, not chosen
   from an unproved mere existence statement. The monoidal model is used to prove the
   existential unit comparison, not to define arbitrary public data.
3. **Split statements: PASS, none.** No new hole, public statement or node is added.
   Checked the private helpers: exact composition, equivalence reflection, and transport
   all prove strictly intermediate claims. Empty opens, zero P and an identity unit map
   need no nonemptiness, boundedness or extra hypothesis. Loogle found the localization
   comparison already used; LeanFinder and source searches found no shorter applicable
   theorem. Analogous homology/localization helpers in `DerivedQCohStandardAdjunction`
   and `SchemeIsoDerivedLocalizations` are private. The independent-universe tensor
   restriction theorem compares objects only, so it cannot replace the natural arrow
   comparison used here.
4. **Route and pruning: PASS after report correction.** Read the original dependency
   declarations and the unit's `realized` record (empty statement list and one empty
   step list). The proof retains the monoidal, quasi-coherent and restriction route.
   Each added import supplies declarations used in the proof and is proof-only.
   Corrected `## No longer needed` to name `def-pc-perfect-complex` as the removed proof
   dependency while retaining its statement dependency and public module import.
5. **DAG: PASS.** Only `proof`, `proof_deps` and `proof_origin` differ from the repository
   node. The union of the proof steps' `uses` is exactly `proof_deps`; the added
   `lem-sc-perfect-qcoherent` corresponds to the theorem applied in the Lean proof.
   No unit or statement record changes, and no new node is needed for a split hole.

Second reading changed only the pruning report and added this review. The Lean proof and
node were retained.
