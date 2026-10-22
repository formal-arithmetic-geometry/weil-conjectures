# Repair assignment: proper Qbar coefficient comparison

Issued by pipeline maintenance, 2026-10-22, for
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
This is a scoped correction assignment, not a proof or a certification of a
counterexample. It applies to whichever group holds the module.

## Cause and evidence

The B5 delivery landed at `a898901fa56` with the existing proper/unbounded
instance marked `STATEMENT-DISPUTED`. B4 was subsequently dispatched as ordinary
proof work at least 36 times. `deliver3.py` correctly sees no newly disputed
statement and no closed assigned hole, and rejected the preserved packet with
`FAILED: nothing is proved` before review. No repair or upstream correction had
been recorded. Repeating the same dispute cannot repair that mismatch.

The missing input is exact: step 2 of `lem-sfb-qlbar-push-iso-proper` asserts
ambient coproduct continuity from properness, with `uses: []` and
`elementary: null`. The existing proved private criterion identifies the
coefficient comparison with the relevant scalar-basis copower comparisons.
The B5 report supplies further counterexample analysis, but explicitly does
not give a Lean-certified refutation of the precise internal-module instance.
Do not strengthen that evidence into a claim that has been formally verified.

## Authorized repair

Read the current source, the B5 report, and the retained B4 packet before
editing. The repair entry admits work that closes zero assigned holes; it
requires an actual correction, not an unchanged dispute packet or a rebase.

The exception in `coord/upstream-statement-exceptions.tsv` permits changing
only the signature of
`isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper`
in the assigned upstream module. Replace the unsupported implication from
properness alone by a proved comparison under an explicit sufficient
continuity hypothesis (the existing copower criterion is available). A
bounded-below, objectwise formulation is also permitted if its exact
hypotheses and canonical comparison are justified by the available library.
Retain the declaration name, the finite-extension result, public imports, and
every unrelated signature. Update the affected docstrings and the anonymous
Qbar Shriek example in the same file: it must carry the corresponding
hypothesis on the proper part of its compactification, or the appropriate
objectwise bounds. It must not continue to infer the blanket ambient result.
New public supporting declarations belong in `Sheaf/` as usual.

This assignment specifically authorizes documenting the necessary correction
to clause 3 and its Shriek consequence in
`sk-prop-sfb-finite-extension-compatibility`. The general requirement to retain
a unit's route is not a requirement to prove this already-disputed clause from
properness alone. Preserve the original unit record as source history; name
the original and corrected clauses explicitly in the change record. Do not
claim the original all-unbounded unit statement has been realized. Unit-record
edits are maintainer-owned and must be identified for the independent reader
and maintainer to reconcile with the reviewed correction; the worker delivery
tool does not transport edits to `dag/units/`.

Reconcile `lem-sfb-qlbar-push-iso-proper` with the corrected Lean signature,
including `statement_change`, the Lean attachment, the actual proof, and its
dependencies. Audit every DAG citer and every direct Lean importer, including
implicit typeclass consumers. Supply the normal `coord/changes/` record and
adapt forced callers together. An importer may use the bounded-below theorem
already proved in the B4 companion packet when its hypotheses really hold.
Do not hide a missing continuity argument in a new `sorry`, restore the
unconditional instance in another module, or silently weaken a caller.

The finite E-to-F clause and the other unit steps remain obligations. The
target statements, `Challenge.lean`, and their meanings are unchanged. This
assignment grants no other upstream signature exception. If another public
signature must change, give its precise dependency and required correction
for maintainer review rather than extending the exception list yourself.

## Delivery and handoff

Use the ordinary delivery command after completing the correction. Report
changed statements as corrections, not closed proofs of their old statements.
The change record, node updates, accompanying module and explicit
`STATEMENT-DISPUTED:` discussion send the packet to independent CODEX review.
Compile on the server one file at a time through `tools/lean_file.sh`, within
60 seconds per file; do not run `lake build`.

The existing B4 sandbox contains a compiled bounded-below companion proof and
diagnostic criteria. Preserve and rebase useful work. A companion proof alone
does not resolve the disputed instance. Keep the repair entry until the
correction and its consumers have landed and the normal global verification
has succeeded; the maintainer then removes it and records the reviewed unit
reconciliation. No failure counter, claim, dispatcher or admission setting
needs to change.
