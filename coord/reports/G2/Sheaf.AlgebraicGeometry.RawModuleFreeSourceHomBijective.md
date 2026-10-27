## What changed

Complete the explicit zero-hole retirement assignment from coord/retire-items.tsv.
Withdraw Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective through deleted.txt
and attach lem-sbc-raw-module-free-source-hom-bijective to the already proved
WeilConjectures.AlgebraicGeometry.RawModuleFreeSourceHomBijective theorem
AlgebraicGeometry.Etale.rawModuleFreeSourceHom_bijective.

The adopted upstream statement differs only by writing moduleAbelianForget in
place of its existing abbreviation RawModuleScalarComparison.forget. A scratch
Lean example retains the complete original statement and applies the upstream
theorem directly. The node's mathematical statement, proof, proof dependencies
and unit route remain in force. The two parent nodes already point to upstream
consumers that import and apply this same theorem.

No source-library file or target statement changes. No consumer adaptation is
needed: tools/downstream.py finds zero downstream modules of the Sheaf copy,
and independent live-source and quarantine searches find zero importers.
Change record: coord/changes/G2-retire-raw-module-free-source-hom-bijective.md.

## Proved and sorry left

The assigned module has zero sorry holes before withdrawal. Holes closed: none
(0 of 0). Holes added: none. Holes left in the delivery: none. No split-off
statements or new mathematical claims. The already complete upstream proof of
AlgebraicGeometry.Etale.rawModuleFreeSourceHom_bijective remains the proof of
the mathematical node. Its four private helpers have complete proof/data bodies
and require no replacement public declarations.

Server validation: scratchpad/VerifyCanonicalComparison.lean compiled cleanly
through lcompile.py in 8.4 seconds. Its example proves the exact old statement
by applying the upstream theorem. It also imports both actual upstream parent
modules. The axiom audit for rawModuleFreeSourceHom_bijective,
rawModuleAbelianHomMap_injective and rawModuleAbelianHomMap_surjective reports
exactly propext, Classical.choice and Quot.sound for each; no sorryAx occurs.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.RawModuleFreeSourceHomBijective. Its
public import of Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso is
removed with the duplicate module. That dependency module remains needed
elsewhere; this delivery makes no claim to prune it.

The duplicate public theorem and private abelianSections, abelianSections_comp,
freeMap_sections and scalar_unit declarations are removed with the Sheaf copy.
The canonical upstream theorem and its private section-comparison proof remain.
No mathematical DAG node, proof dependency or upstream module is pruned. Both
parents continue to use lem-sbc-raw-module-free-source-hom-bijective, now attached
to its actual upstream implementation.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes an unfinished proof, but this item is an
explicit retirement with zero holes. Its node still pointed to the duplicate
Sheaf theorem even though both mathematical parents already use the upstream
theorem. This delivery repairs that stale attachment before withdrawal.

The retirement inventory lists two historical Sheaf consumers,
RawModuleAbelianHomMapInjective and RawModuleAbelianHomMapSurjective. Neither
exists in the live Sheaf tree or quarantine; their node attachments and actual
proofs are already upstream. Both upstream proofs still use the theorem being
retained. No matching rework/quarantine entry or current return exists for this
item; no absent archive is deleted or replaced.

The inventory also lists an absent pullback_unit_hom helper. The current item
contains no such helper, and its four remaining helpers are private. Its sole
public signature is definitionally identical to the adopted upstream theorem.
The proof dependencies remain the canonical scalar comparison and represented
free-sheaf sections; no unit-level route is bypassed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
