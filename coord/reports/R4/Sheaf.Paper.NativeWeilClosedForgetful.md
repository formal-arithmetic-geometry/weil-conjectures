## What changed

Repaired `AlgebraicGeometry.ProEtaleWeilSheaf.NativeAdjunctionNormalization` in
`Sheaf.Paper.NativeWeilClosedForgetful`, the item listed as disputed in the current
queue. Removed the extra `(p * q).negOnePow` scalar from the component equation
for uncurrying a degree-zero map into the native row-sign Hom complex. Updated
the docstring and removed the two dispute comments resolved by this correction.
The separate Koszul sign for tensor symmetry is retained.

Change record: `coord/changes/native-adjunction-row-sign-normalization.md`.
The node's Lean realization note records the corrected convention and the need
for renewed semantic review of affected targets. The mathematical node statement,
its proof plan, dependencies and unit route are unchanged. No target text changes.

The change has no direct external references to the normalization definition.
The seven downstream modules listed in the change record inherit its meaning
through NativeOrdinaryTensorModels and NativeClosedComparison. Their uses request
canonical tensor/Hom structures and evaluation compatibility; none uses the
removed scalar in an argument. No adaptation of their source is necessary.
The induced semantic change repairs their previous impossible normalization and
requires review; it is not claimed to leave that old erroneous predicate equivalent.

## Proved and sorry left

This is a definition repair, not a proof or decomposition of the main theorem.
Closed zero holes; added zero holes; split off zero statements. The only remaining
hole is `AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful`, attached to
`lem-sf-weil-native-closed-forgetful`. Its proof remains exactly `by sorry`.
The four previously proved additivity instances are preserved verbatim.
No data is postponed in a definition and no axiom is introduced.

## No longer needed

None. No imports, nodes or modules are pruned. In particular, the existing native
assembly dependencies remain needed by the unfinished main proof. The exploratory
assembly files are scratch work only and are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The former normalization used the standard-Hom Koszul uncurrying factor with the
native row-sign Hom differential. These are different conventions. The native
projection differential is (-1)^p(d_I f - f d_P), whereas mapBifunctor P Q has
first differential d_P and second differential (-1)^p d_Q. For a degree-zero
chain map Q -> Hom_native(P,I), componentwise adjunction is therefore unsigned.
The tensor bifunctor's reversed underived values do not change the total's index
order. The signed swap still requires (-1)^(p*q).

The counterexample and corrected odd-degree chain square are recorded in the
change record. They recover the precise diagnosis in E1's report. Independently,
the source library's proved
`CochainComplex.ιTensorObj_internalHomEquiv_symm_f` has unsigned degree-zero
uncurrying for the same convention; its general cochain factor is (-1)^(p*n),
with n the cochain degree. Checking zero complexes, empty summands, degree zero,
even parity and odd/odd inputs gives the expected behavior. The old stage-2 sign
check missed this differential test. This repair resolves that defect rather
than weakening the intended closed tensor/evaluation assertion.

The DAG citers remain mathematically valid: NativeOpenDerivedTensor uses open
restriction of the canonical closed structure; native-proper-projection-realization
uses the tensor comparison; the Verdier-dual preservation and biduality nodes use
canonical evaluation and transpose; DerivedWeilOperations installs the canonical
operations; NativeWeilDualizingHomTransposition uses the transpose normalization;
WeilGeometricHomConstructibility uses the underlying Hom comparison;
weil-dual-realization-comparison and weil-bidual-evaluation-realization use the
same evaluation comparison; NativeDerivedWeilTensorConstructible uses the tensor
comparison and constructible restriction. None prescribes the removed native
chain-level scalar. Their statements and the unit's realized route require no mathematical change. Affected target
statements must nonetheless receive the normal semantic re-review because the
Lean definition below them changed.

Validation from the retained attempt: lcompile compiled the repaired item in 41.4 seconds and its
unchanged consumers DerivedWeilOperations (28.6 seconds),
WeilGeometricHomConstructibility (51.3 seconds), and
NativeDerivedWeilTensorConstructible (55.0 seconds) against the repaired overlay.
NativeOpenDerivedTensor reached its 60-second limit; an unchanged-baseline check
was requested to distinguish this from an effect of the normalization repair.
The remaining consumer checks were stopped by that timeout, not passed.

Delivery tool failure: `deliver3.py R4 Sheaf.Paper.NativeWeilClosedForgetful`
refused this definition repair with `FAILED: nothing is proved`, because the sole
main theorem still has its sorry. The current queue lists this item as disputed;
the packet corrects its disputed definition, compiles, and reports zero holes
closed. The launcher's admission gate accepts closed holes, newly added dispute
markers, declaration-signature changes, or its specific repair-list records. It
does not recognize this body-only correction of an already disputed definition.
No launcher script was edited, no synthetic signature change was made to bypass
that gate, and nothing was pushed. The packet remains available for review.

Resumed verification (2026-10-24 UTC): compared the retained packet with current
sources and current claims; the sole Lean difference remains the sign repair and
its explanatory comments. Re-ran downstream.py: seven consumers, no external
direct reference to NativeAdjunctionNormalization. Rechecked the proved source
uncurrying formula and the actual bifunctor Hom differential. The repaired item
compiled again through lcompile.py, exit code 0, in 27.8 seconds. The required
initial deliver3.py run again exited 1 with FAILED: nothing is proved, before
compilation/preflight/push. Its admission gate still does not recognize this
body-only correction of an already disputed definition. No launcher or metadata
was changed to bypass it. A fresh unchanged-consumer compilation batch was also
requested and remained pending when the delivery refusal arrived.

Resumed verification (2026-10-24 22:00 UTC): the current item still differs only
by the retained sign correction and the resolved dispute comments. The repaired
item compiles through lcompile.py (exit 0, 27.8 seconds). All seven consumer
copies match current source byte for byte. The refreshed consumer overlay
compiles DerivedWeilOperations (4.1 seconds), WeilGeometricHomConstructibility
(46.2 seconds), and NativeDerivedWeilTensorConstructible (46.6 seconds);
NativeOpenDerivedTensor again reaches its 60-second limit. An unchanged baseline
comparison and individual checks of the remaining consumers are pending. The
required initial deliver3.py invocation is still pending; no new gate result or
push is claimed. The current downstream audit again finds no external direct
reference to NativeAdjunctionNormalization. The proved source formula
ιTensorObj_internalHomEquiv_symm_f and bifunctorHomObj_d_π confirm the unsigned
degree-zero component convention.

Final delivery result for this resumed attempt: deliver3.py exited 1 with
`FAILED: nothing is proved`, naming native_closed_forgetful as still having its
original hole. This is the same admission defect as the earlier two attempts:
the documented definition-repair exception is not recognized for this already
disputed, body-only normalization correction. Nothing was pushed and no tool,
claim, repair registry or declaration signature was altered to bypass the gate.
The repair packet, its change record and its node note are retained.

Additional consumer evidence: the unchanged-baseline NativeOpenDerivedTensor
check could not reach that module because the compile overlay's current
WeilFrobeniusActionResolutions dependency timed out after 60 seconds. The
WeilCompactStructureTensorComparison check stopped because its
NativeOpenDerivedTensor dependency timed out after 60 seconds. These are
incomplete consumer checks, not successful compiles and not the delivery blocker.
The dependent modules require no textual change for this normalization repair;
independent review and the normal global build remain required after the
admission gate is corrected.

Resumed verification (2026-10-24 22:36 UTC): re-read the current item, node,
unit, stage-3 contract, rework and repair registries, and downstream audit. The
retained repair still changes only the erroneous normalization scalar and its
explanatory/dispute comments; all original declarations and public imports stay.
Both source and repaired module contain exactly one hole, in
`AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful`; zero holes closed,
zero added, zero split off. The repaired item again compiled through lcompile.py
with exit code 0 (cached server result, 27.8 seconds). All seven consumer copies
remain byte-identical to their current source modules. The source lemmas
`ιTensorObj_internalHomEquiv_symm_f` and `bifunctorHomObj_d_π` again confirm the
unsigned degree-zero convention.

The required initial deliver3.py invocation completed with exit code 1 and
`FAILED: nothing is proved`, before compilation/preflight/push. Inspection of
its existing admission condition confirms that it accepts registered repairs,
new dispute markers, signature changes or closed holes, but does not recognize
this body-only correction of an already disputed definition. The current item
has no entry in repairs.txt, rework.tsv, retire-items.tsv or the group's return
headings. This is a launcher admission defect under the explicit definition-repair
exception in the worker brief and stage-3 contract. No launcher script, claim,
repair registry, budget or declaration signature was altered to bypass it.
Nothing was pushed; the concrete repair, change record and node note are retained.

Three refreshed consumer checks were submitted for
NativeWeilDualizingHomTransposition, NativeCompactProjectionFormula and
WeilCompactStructureTensorComparison. They remained pending after the admission
refusal; no additional successful compile is claimed. Their lcompile result IDs
are 1387a4a8546989482c6ee49f, 5580d32888b2d8eb298a9de3 and
cbe8b4e0613a72945ac84c55, respectively.


Resumed verification (2026-10-24 22:52 UTC): retained the packet and compared it
with the current item and node. The only Lean changes remain the unsigned
uncurrying correction and its comments. Rechecked all current consumer copies:
the seven copies are byte-identical to current sources; the item copy matches
the repaired item. Current holders remain U4 for DerivedWeilOperations, T8 for
WeilGeometricHomConstructibility, R4 for the item, and unclaimed for the other
five consumers. The item again compiles through lcompile.py, exit 0 (cached
27.8-second result). The current downstream audit still lists seven consumers
and no external direct references to NativeAdjunctionNormalization. Both source
and repaired item contain one sorry, native_closed_forgetful; zero holes closed,
zero added. Refreshed checks of NativeWeilDualizingHomTransposition and
NativeCompactProjectionFormula stopped at their NativeOpenDerivedTensor
prerequisite's 60-second timeout. These are incomplete consumer checks, not
successful compiles or evidence that the normalization repair caused a failure.
The required initial delivery invocation remains pending; no new result or push
is claimed at this point.


Final delivery result of this resumed attempt: the required initial
`deliver3.py R4 Sheaf.Paper.NativeWeilClosedForgetful` invocation exited 1 with
`FAILED: nothing is proved`, naming the original native_closed_forgetful hole.
The delivery stopped before compilation/preflight/push. Its admission condition
still recognizes closed holes, new disputes, signature changes and registered
repairs, but not this body-only correction of an already disputed definition.
The current item has no repairs.txt, rework.tsv or group-return entry to enable
that exception. This remains the launcher admission defect reported previously;
no launcher code, repair registry, claim, budget or declaration signature was
changed to bypass it. Nothing was pushed. The compiling repair, change record,
node note and report are retained in the sandbox for independent review.


Resumed verification (2026-10-24 23:19 UTC): retained the existing repair,
change record, node note and scratch work. Compared the item and node with
current sources: the only Lean change is the unsigned degree-zero uncurrying
correction and its associated explanatory/dispute comments. The repaired item
again compiles through lcompile.py, exit 0 (cached 27.8-second result). Source
and repaired item each have one hole, native_closed_forgetful; zero holes
closed, zero added and zero split off. The source's proved
ιTensorObj_internalHomEquiv_symm_f again confirms the unsigned formula.
The downstream audit again gives exactly seven consumers and no external
direct references to NativeAdjunctionNormalization. Their retained source
copies remain byte-identical to current sources; the overlay item matches
the repair. Current holders in the change record are still correct.
Fresh checks of DerivedWeilOperations, WeilGeometricHomConstructibility,
NativeDerivedWeilTensorConstructible and NativeOpenDerivedTensor were submitted
and are pending. The required initial deliver3.py invocation is also pending;
no new refusal or push is claimed yet. The current admission condition still
recognizes closed holes, new disputes, signature changes and registered repairs,
but not a body-only correction of an already disputed definition. The current
queue lists this item as disputed; it has no repairs.txt, rework.tsv,
retire-items.tsv or group-return entry. No launcher script or admission metadata
was changed, and no synthetic signature change was made.


Fresh consumer results in this resumed attempt: DerivedWeilOperations compiled
in 12.7 seconds, WeilGeometricHomConstructibility in 4.7 seconds,
NativeDerivedWeilTensorConstructible in 2.1 seconds, and
NativeOpenDerivedTensor in 16.7 seconds, all exit 0 against the repaired overlay.
The latter used the current privately compiled unpublished
WeilFrobeniusActionResolutions dependency; its earlier timeout no longer occurs.
The remaining three consumer checks and the initial delivery invocation are
still pending. No delivery success is claimed.


Final delivery result (2026-10-24 23:42 UTC): the required initial invocation
of deliver3.py exited 1 with `FAILED: nothing is proved`, naming the unchanged
native_closed_forgetful hole. It stopped at admission, before delivery
compilation/preflight/push. This repeats the documented launcher admission defect:
the body-only correction of an already disputed definition is not accepted,
despite the explicit definition-repair exception in the worker brief and
coord/brief-stage3.md. The packet is a substantive correction, not a no-op;
zero holes closed and zero added are reported honestly. No launcher scripts,
repair registries, claims, budget or signatures were altered to bypass the gate.
Nothing was pushed. The repair, node note, change record and report are retained.
Four fresh unchanged-consumer compiles passed as recorded above; checks for
NativeWeilDualizingHomTransposition, NativeCompactProjectionFormula and
WeilCompactStructureTensorComparison remain pending at this delivery refusal.

Resumed verification (2026-10-24 23:53 UTC): the mandatory initial delivery
check exited 1 with `FAILED: nothing is proved`, naming
`AlgebraicGeometry.ProEtaleWeilSheaf.native_closed_forgetful`. The refusal occurs
before compilation/preflight/push. The repaired item independently compiles
through lcompile.py, exit 0 (cached 27.8-second result). The current source and
packet each contain exactly one sorry; zero holes closed, zero added, zero split
off. The only Lean changes remain the unsigned degree-zero uncurrying correction
and the associated explanatory/dispute comments. All seven consumer source
copies still match current sources byte for byte; the consumer-overlay item
matches the repaired item. The node differs only in its Lean realization note.
Current claim holders and downstream audit agree with the change record.
Read the current blueprint's evaluation/transposition proof and the proved
source uncurrying and Hom differential equations again: the sign correction
retains the intended canonical closed structure and unit route.

The admission condition in deliver3.py recognizes closed holes, newly added
disputes, signature changes, repair/return/rework/retirement entries and repair
jobs. This already disputed body-only definition correction is not recognized;
the current registries contain no qualifying entry. The documented definition
repair exception therefore remains inaccessible for this packet. No launcher
code, registry, claim, budget or signature was changed to bypass the gate.
A refreshed combined consumer-overlay check is running through lcompile.py;
its result will be recorded below. Nothing was pushed.

The refreshed combined consumer check stopped before compiling the item:
its current privately compiled WeilFrobeniusActionResolutions prerequisite
exceeded 60 seconds (lcompile exit 124). This is a dependency compile timeout,
not 'no answer from the compile server', not a successful consumer check, and
not the reported delivery blocker. The separate item compile above succeeded.
The delivery blocker remains the admission gate's `FAILED: nothing is proved`
for the substantive definition repair; no delivery compilation or push occurred.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
