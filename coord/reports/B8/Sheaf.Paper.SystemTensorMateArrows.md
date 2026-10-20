## What changed

Repaired the returned delivery against the current post rollback source of
`Sheaf.Paper.SystemTensorMateArrows`. The packet retains the completed
coefficient, additive, K-injective, lax-tensor and direct-composition proofs,
and proves `Operations.alpha_existsUnique` from the existing varying-ring
proper/open operations.

The reapplication also replaces the duplicate continuity and ordinary open-unit
arguments with existing varying-ring theorems. For the open unit, identify the
specified direct image, then use uniqueness of adjoints to compare both supplied
left adjoints. Their composite is isomorphic to the identity, so Mathlib's
`Adjunction.isIso_unit_of_iso` gives the required unit isomorphism. This removes
about 300 lines of private slice/site/adjunction support from the retained
packet and removes its `Adjunction.Triple` import.

For alpha, open base change and composition put the source and target in the
pullback open. The further lift is clopen. Open-extension and clopen-direct-image
adjunction identities make restriction bijective on the relevant Hom set.
Transport across the supplied adjoints and uniquely lift the prescribed natural
word. Injectivity gives naturality and uniqueness. All comparisons occur in
ordinary system categories before localization; nonflat quotient transitions
and noncartesian input squares are permitted.

Every original public signature, definition body, attribute and public import
is unchanged. All added imports are private proof imports; all new declarations
are private and completely proved. The current node's proof, proof dependencies
and proof origin are updated, with all other metadata preserved from current
main. The change record
`coord/changes/H8-system-tensor-mate-proof-scopes.md` documents
declaration-scoped commands and proof support.
No new module or consumer adaptation is included.

Validation: the final complete sandbox module compiled through `lcompile.py`
in 33.6 seconds (the preceding shortened version compiled in 33.2 seconds).
All delivered Lean lines are at most 100 characters. Identity and empty-open
cases use the same adjunction identities. The delivery additionally runs the
compiler probe, axiom audit and server preflight.

## Proved and sorry left

Closed 8 of the 10 holes present in the current post rollback repair base:

- `WeilConjectures.SystemTensorMate.base_continuous`
- `WeilConjectures.SystemTensorMate.coefficient_existsUnique`
- `WeilConjectures.SystemTensorMate.direct_additive`
- `WeilConjectures.SystemTensorMate.system_kInjective`
- `WeilConjectures.SystemTensorMate.laxTensor_existsUnique`
- `WeilConjectures.SystemTensorMate.directComp_existsUnique`
- `WeilConjectures.SystemTensorMate.Operations.ordinaryOpenUnit_isIso`
- `WeilConjectures.SystemTensorMate.Operations.alpha_existsUnique`

Added 0 holes; split off 0 statements. These are proofs from existing declared
library dependencies, including dependencies with their own unfinished proofs.

The two original holes left unchanged are:

- `WeilConjectures.SystemTensorMate.tensorOperations_nonempty`
- `WeilConjectures.SystemTensorMate.TensorOperations.deltaInv_isIso`

Both retain their original statements and complete proof plans. They require
transport of the supplied arbitrary tensor models to normalized system-level
operations; no transport was added as an assumption or claimed proved here.

## No longer needed

Removed the retained packet's private import
`Mathlib.CategoryTheory.Adjunction.Triple`. The item proof no longer needs
`lem-pur-proetale-open-unit-evaluation`: the varying-ring ordinary open-unit
theorem and uniqueness of adjoints replace the duplicate open-site construction.
The theorem's library module and its other consumers are preserved.

No module, node or declaration is withdrawn. In particular the quarantined
consumers `SystemClopenTensorCompatibility`,
`SystemCompactificationProjectionSubstitution` and `FiniteFreeCompactComposition`
remain preserved, as do all existing public exports including `FiniteFieldDatum`.
All other declared dependencies and public imports remain needed.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified a moving-base conflict: current main contains
ten holes after the batch rollback, whereas the earlier base contained three.
The current report and packet therefore account for all eight completed proofs,
including the seven proofs carried over from H8. The unit's route and all
statements are unchanged. Existing varying-ring declarations give shorter
continuity and open-unit proofs than the retained duplicate site constructions.

The first reapplication preflight requested the missing Status section of the
change record; it is now present. Compiler timeouts prompted removal of the
duplicate open-site construction; the shorter complete module compiles below
the unchanged limit. A mistaken path briefly wrote the shared source; it was
restored to the checked-in current file, and subsequent work stayed in the
assigned sandbox.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
