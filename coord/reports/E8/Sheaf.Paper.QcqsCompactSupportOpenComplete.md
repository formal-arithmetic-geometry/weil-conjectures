## What changed

Proved `WeilConjectures.sfQcqsCompactSupport_open_complete` in
`Sheaf.Paper.QcqsCompactSupportOpenComplete`, preserving its complete signature and public
imports. Added four proof imports: `SfIntegralCompactSupportConstructible` (private
intrinsic/unrestricted completeness comparison), `SfCompleteDirectImageReduction`
(private isomorphism invariance), `OpenQuotientKoszulCompleteness`, and
`OpenDvrRingedIdentification`. The first two use `import all` to access their proved helpers.
The DAG proof now records the actual argument. A declaration-local unused-section-variable
linter setting preserves the original geometric binders, several of which the shorter proof
does not need.

The open factor is quasi-compact by the compactification API. The structure maps carry the
unit ell from the arbitrary base field to global sections of both endpoints. The existing
quotient/Koszul theorem supplies completeness of the DVR open model; the existing natural
identification with ringed open extension and isomorphism invariance finish the proof.
The first single-file compile passed in 4.2 seconds; final delivery checks validate the
version with the declaration-local linter setting.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.sfQcqsCompactSupport_open_complete`
(node `lem-qcqs-compact-support-image-complete-open`).
No sorry remains in the item. Added 0 holes and split off 0 statements.
This is a proof from existing declarations, not a new decomposition. The reused theorem
proofs may still depend transitively on existing project obligations.

## No longer needed

None: no imports removed, no modules withdrawn, and no previously recorded dependency nodes
pruned (the item's original `proof_deps` was empty). No new tower-transport lemmas are needed:
the existing quotient-completeness and normalized functor-identification results suffice.
The existing public imports remain to preserve the module's public interface.

## Where the brief, the DAG or earlier work was wrong

The node's plan had no declared proof dependencies despite existing suitable declarations.
Its proof dependency list now names the quotient/Koszul completeness assembly, the
DVR/ringed identification, intrinsic/legacy comparison, and Roos isomorphism transport.
The item did not require a fourth split. No statement or definition was changed, and no
additional separatedness or finite-field assumption was introduced. The unit record
`sk-def-sf-operations` has no realized steps to bypass. The open and identification theorems
are tools from the six-functors compatibility unit implementing the same open-extension
argument; they do not replace a fixed unit route. Empty and identity opens are covered by
the reused general theorems.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
