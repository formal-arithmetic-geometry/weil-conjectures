## What changed

Restored the quarantined module Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore
and repaired Algebra.strictHenselization_surjective_quotient_core. The source and restored
signatures were compared byte for byte and are identical; the public and proof imports
are unchanged. The retired existential quotientBaseChange_obj_iso call is replaced by
an explicit quotient B-action, its compatibility equation, and the proved upstream
quotientBaseChangeObjIso. The final-functor and preserved-colimit argument is retained.
The existing node's last proof step and proof_origin now describe this construction.
The unit sk-prop-input-spreading and its route are unchanged.

The action descends the explicit map A -> C/IC with RingHom.liftOfSurjective; no object
is selected from an unproved existence theorem. The proof works unchanged when I = 0
or C/IC is the zero ring. Mathlib searches via msearch.py covered leanfinder, loogle,
and grep. Loogle found liftOfSurjective and its composition lemmas. Source search found
the proved quotientBaseChangeObjIso; its explicit compatibility input is the API gap.

Validation: lcompile.py compiled the repaired core in 1.6 seconds. A subsequent --all
check compiled the core in 1.5 seconds and the unchanged archived direct consumer
Sheaf.RingTheory.StrictHenselizationSurjectiveQuotient in 1.4 seconds. The temporary
consumer copy and axiom-print command are not in the delivery. The axiom check of
Algebra.strictHenselization_surjective_quotient_core reports exactly propext,
Classical.choice, and Quot.sound.

Change record: coord/changes/strict-henselization-quotient-core-K1-20261020.md.

## Proved and sorry left

This is a zero-hole quarantine repair. Holes closed: 0 of 0. Holes added: 0.
Split off: 0. Sorries left in all delivered Lean files: 0.
Algebra.strictHenselization_surjective_quotient_core is a complete, compiling proof
with the unchanged statement. Its only axioms are the three permitted standard axioms.
No other declaration is changed or introduced.

## No longer needed

No imports, modules, or nodes are pruned. Both declared dependencies remain used:
lem-sbc-pointed-etale-quotient-final and lem-sbc-surjective-quotient-base-change.
The unavailable quotientBaseChange_obj_iso API is no longer called; it is replaced
by the proved upstream quotientBaseChangeObjIso and elementary quotient descent.
No compatibility declaration or new module is needed.

## Where the brief, the DAG or earlier work was wrong

The item has zero sorries and is absent from lean/ because it was quarantined, not
withdrawn. The assigned failure is the old quotientBaseChange_obj_iso identifier.
The replacement API also changes how the action is supplied: it requires constructing
a compatible action and proving its composition equation, not just renaming the call.
The node's proof now states that missing elementary descent step explicitly.

The earlier retirement record for the quotient-base-change copy scanned live lean/
only and reported no consumers; the quarantined core was still a consumer of the old
name. This delivery repairs that preserved consumer without restoring the duplicate.
The current downstream.py scanner cannot find a quarantined item; the consumer check
therefore scanned both live and archived Lean sources and compiled the archived direct
consumer unchanged. The declaration and its Lean attachment and dependencies are retained.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
