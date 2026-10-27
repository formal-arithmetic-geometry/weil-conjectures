## What changed

Added three proved conditional obstruction theorems to the item module:
`CategoryTheory.BrownHypothesesFor.finite_nonzero_hom_of_product_coproduct`,
`CategoryTheory.not_brownHypothesesFor_of_product_coproduct`, and
`CategoryTheory.not_brownHypothesesFor_of_positive_ext`.

The first shows finite support of nonzero Hom groups into a family whose coproduct is
also its product. The second refutes Brown's bundle when that support is infinite. The
third builds the required product-coproduct from the positive shifts of a degree-zero
module, using exact countable products of pro-etale module objects. Its source is the
existing derived-category nonpreservation argument. This makes the categorical part
of the disputed statement's counterexample diagnostic a checked library theorem.

Added proof-only imports of the derived-products API and the pro-etale exact-countable-
products instance. An explicit dependent Hom-family argument disambiguates the old
`Limits.Sigma.desc`/`Pi.single` application in the generation helper after the new imports. Added two nodes for the new theorems and a diagnostic proof step in
the item's node. Existing statements, definitions, public imports and visibility are
preserved. The original arbitrary-field assertion remains disputed and sorry.

On resumption, the rework table still lists the item, but the quarantine path is absent
and the original Lean path has already been restored in the shared checkout. Comparing
the preserved packet against that current source shows only the two proof imports,
the explicit dependent-family argument, and the three obstruction theorems above.
All restored declarations and their signatures are retained; no archive is deleted.
The required delivery command was restarted before further packet changes, and the
prescribed compile command again returned exit 0 for the preserved module.

The landed declarations cited are `brownHypothesesFor_iff`,
`isCompactObject_iff_isCompactObj`, `CochainComplex.isLimitFanMkProjSingleFunctorObjShift`,
`DerivedCategory.isColimitCofanMkQObj`, `DerivedCategory.isLimitFanMkQObj`, and
`CondensedRing.countableAB4Star_mod`. There is no copy of a landed theorem: the source
nonpreservation result concerns a functor defined on the entire derived category;
our result concerns compactness inside its constructible localizing full subcategory,
and explicitly lifts both universal properties into that subcategory.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added: 0. Split-off holes: 0.
The only remaining sorry is `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`, in its original signature. The three new theorems have complete
proofs and introduce no geometric compactness assumption disguised as a theorem.
This packet is a conditional counterexample criterion, not a proof or decomposition
of the original arbitrary-field assertion.

The prescribed `lcompile.py` compiled the final item cleanly in 45.6 seconds, exit 0,
with no warnings. All three new proofs are complete. A separate source-containing axiom probe compiled in 35.9 seconds, exit 0. For each
of the three new theorem names, `#print axioms` lists exactly `propext`,
`Classical.choice`, and `Quot.sound`. The initial import-only scratch probe could not
see sandbox declarations and was replaced by this direct source probe. The delivery
tool's own axiom/preflight checks remain the submission gate.

The first `deliver3.py` invocation returned exit 75, `DELIVERY BUSY`: all six
priority delivery slots were occupied for its 50-minute managed wait. It pushed
nothing. After the prescribed pause, the unchanged packet was submitted again. The second
invocation also returned exit 75 with the same six occupied priority slots after its
50-minute managed wait. Neither attempt reached preflight or pushed anything; the
verified source is preserved. A third invocation, after another prescribed pause,
also returned exit 75 after its 50-minute managed wait with all six priority slots
occupied. Three attempts therefore failed before preflight or push. This is a
submission-capacity tool blockage, not a compile timeout: the final module compiled
cleanly in 45.6 seconds and its separate axiom probe passed in 35.9 seconds.
Earlier standalone compile processes ended with signal 143 and no compiler result;
the subsequent successful compile supersedes those interruptions.

The resumed worker ran the required delivery command first. This fourth attempt also
returned exit 75, `DELIVERY BUSY: 6 deliveries are running on this machine; retry in a
few minutes`, after its 50-minute managed wait. It reached neither preflight nor push.
The prescribed compile and source-containing axiom probe were both rechecked during
this attempt and returned their successful results. No launcher files, slot settings,
locks or budget metadata were changed. The packet is preserved for resubmission.

The current resumed session again started with the required delivery command before
changing the packet. Its source comparison confirms that all original signatures,
definition bodies and public imports match the restored current source. The prescribed
compile and source-containing axiom probe return their successful cached results
(45.6 s and 35.9 s respectively); each new theorem uses only the three allowed axioms.
There is exactly one original proof hole and no added holes. The current submission
is pending; no successful push is claimed in this report.

The resumed source-only consumer census finds 379 transitive downstream modules,
superseding the earlier 229-module list in the change record. Direct calls remain
in ExceptionalInverseImageExistence (one) and LocalizingExceptionalAdjoint (two).
The change record lists the complete updated census; none needs adaptation because
every original signature, definition and public import is preserved.

## No longer needed

No imports, modules or existing dependency nodes are pruned. The finite-field assembly
still needs its compactness and smallness modules. The source nonpreservation theorem
is read as the argument's source; it is not imported, because the new proof constructs
the full-subcategory product and coproduct directly. Both added imports are used for
the positive-Ext criterion. The live and archived parent dependencies are preserved.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `brownHypotheses` asserts compactness over arbitrary positive-
characteristic fields, while its compactness dependencies require an algebraic closure
of a finite field, or a separate cohomological bound. The current standing blueprint
setting explicitly says no further field hypothesis is imposed. Its admissibility
predicate also contains the distinct all-continuous-map algebraic-closure coefficient,
which the six-case finite-field compactness declaration does not cover.

The existing mathematical diagnostic is k = algebraicClosure(F_3)(t_1,t_2,...), ell=2,
X=Spec k and the rank-one constant F_2 coefficient. Kummer cup symbols, detected by
iterated residues, give nonzero cohomology in all positive degrees. The new theorem
proves the categorical contradiction conditional on those nonzero maps. The Kummer
and residue computation is not formalized in this packet; no unconditional Lean
counterexample or field-cohomology calculation is claimed. Consequently there is no
honest application of the finite-field theorem that closes the original hole.

The pre-existing item and criterion nodes refer to `lem-sfb-localizing-closure-generators`,
which has no current JSON file although the public theorem
`localizingClosure_generatingFamily` is present and proved. This packet does not
reassign any landed declaration or other node's attachment.

Edge cases: the finite-support theorem covers empty and finite index types, zero
objects, zero rings and repeated isomorphic summands. The obstruction conclusions
require an infinite support or nonzero maps to every positive shift, so exclude the
zero-object case correctly. All indexing universe lifts are explicit, and the shifts
and Hom groups are the actual ones of the inherited localizing subcategory.

## New nodes

`lem-sfb-brown-product-coproduct-obstruction` records finite Hom support and its
infinite-support contrapositive. `lem-sfb-brown-positive-ext-obstruction` records the
positive-Ext criterion using exact countable products and both lifted universal
properties. Both nodes are proved; neither has a sorry or replaces the original claim.

Change record: `coord/changes/R1-brown-positive-ext-obstruction.md`.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
