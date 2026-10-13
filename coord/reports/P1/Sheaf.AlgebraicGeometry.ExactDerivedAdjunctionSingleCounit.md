## What changed

Closed `CategoryTheory.Adjunction.exact_derivedAdjunction_single_counit` with its original
signature and public imports. Two fully proved local lemmas express the right-derived
unit comparison and identify the transported termwise counit. The final proof uses
Mathlib's `derivedε_fac_app` and composes these identities. Updated the node's proof
text to describe the actual argument. All Lean changes are in the assigned module.
No commands, public imports, declarations or signatures outside the proof body change.

## Proved and sorry left

Closed one original hole:
`CategoryTheory.Adjunction.exact_derivedAdjunction_single_counit`
(node `lem-sc-exact-derived-adjunction-single-counit`).
The local lemmas `hunit` and `hterm` are fully proved.
No holes added, no `sorry` remains in the delivery, and no intermediate obligations
are split off. This is a proof, not a decomposition.

## No longer needed

No original imports or dependency nodes are pruned: the original route is retained.
Removed the inherited sandbox-only proof imports and modules
`Sheaf.AlgebraicGeometry.SingleRightDerivedUnitComparison` and
`Sheaf.AlgebraicGeometry.SingleTermwiseCounitComparison`; their proofs are now local
lemmas in the assigned module. The obsolete report's proposed
`DerivedCounitSingleFactorization` and `SingleCounitUnderivedComparison` modules and
nodes are not delivered or needed. These were never original library dependencies.

## Where the brief, the DAG or earlier work was wrong

The inherited target compiled only against a stale compiled helper. A fresh complete
sandbox compile exposed an unfinished `SingleTermwiseCounitComparison` proof. Its report
also named two obsolete helpers and holes that were absent from the sandbox sources.
Repaired the comparison proof using explicit quotient comparison naturality,
isomorphism cancellation, and the degree-zero/other-degree calculation. The original
DAG plan is sound; no statement or definition has changed. The unit route is retained.

## Second reading by P1

1. **Unchanged interface — PASS.** Compared the entire delivered Lean module with
   the repository version: the only difference is the replacement of the original
   theorem's `sorry` proof. The declaration signature, section variables, universes,
   visibility, docstring, and both public imports are byte-for-byte unchanged. No
   definitions or target statements change; no change record is needed.
2. **Proof and trust — PASS.** Compiled the delivered module locally without errors
   or warnings. A scratch copy with `#print axioms
   CategoryTheory.Adjunction.exact_derivedAdjunction_single_counit` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read both local
   proofs and their final composition. There are no holes, forbidden declarations,
   or data choices from unproved existence statements. Removed obsolete sandbox
   `.lbuild` artifacts and repeated compilation without that overlay to exclude
   reliance on the earlier helper modules.
3. **Split statements — PASS (none).** No new declarations or nodes are delivered;
   `hunit` and `hterm` are local, fully proved parts of the argument. The proof needs
   no nonzero-object, faithful-functor, or boundedness assumption: degree zero uses
   counit naturality, and every other degree uses the zero components of a single
   complex. Thus zero objects and the identity adjunction cause no exception.
4. **Route and pruning — PASS.** Read the imported exact-functor and derived-adjunction
   constructions and searched the library for single/counit comparisons and derived
   counit factorization. The closest other use, `AffineAlgebraExactDerivedCounitIso`,
   proves an isomorphism criterion rather than this canonical single comparison.
   Mathlib's `derivedε_fac_app` and the upstream termwise homotopy counit formula
   supply the direct route already used. Both public imports are required by the
   original statement: one supplies the derived adjunction, the other the exact
   right-derived single comparison. All three original proof dependencies remain
   used, so none is missing from `No longer needed`. The unit record
   `dag/units/sk-thm-picard-duality.json` is unchanged; this supporting comparison
   introduces no bypass of a unit statement or proof step.
5. **DAG agreement — PASS.** Compared the node JSON with the repository version.
   Only `proof` and `proof_origin` differ. Its two steps accurately describe the
   unit factorization and transported termwise counit calculation in Lean;
   `proof_deps` is the union of their `uses` and still names all three original
   dependencies. The statement, Lean signature record, unit, and chapter stay
   unchanged. There are no new nodes requiring additional fields.

Second reading changed only this report and removed obsolete generated sandbox
cache artifacts. No Lean or DAG repair was needed. One original hole is closed,
zero holes are added, and no original library module is pruned.
