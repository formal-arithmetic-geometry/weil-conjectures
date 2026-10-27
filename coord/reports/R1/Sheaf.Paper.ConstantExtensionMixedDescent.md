## What changed

Restored `lean/Sheaf/Paper/ConstantExtensionMixedDescent.lean` from the archive
specified by `coord/rework.tsv`. This is the assigned timeout/definition repair,
not a claim that the mathematical descent argument has been proved.

The choice-based `constantExtensionWeilPush` and `constantExtensionWeilAdjunction`
are now irreducible. Added the proved `constantExtensionWeilPush_eq` equation and
unfolded only that wrapper explicitly to construct the adjunction. Gave
`constantExtensionPointPull` its existing functor result type explicitly. Strict transparency now covers all
these definitions and the counit-component composite; relaxed transparency is
scoped to the final theorem statement, whose change-of-datum typeclass matching
needs it. The actual right-adjoint choice, adjunction, unit, point pullback and
sheetwise morphisms have the same mathematical data and types as the archive.
No imports changed. No adopted source-library module changed.

Updated only the existing node's `lean.declarations` list to include the new,
proved unfolding equation. The node, its theorem statement, its proof plan and
its parent/unit dependencies remain in place. The change record is
`coord/changes/R1-constant-extension-adjoint-transparency.md`.

The archived source already compiles against today's published dependencies:
6.7 seconds without profiling, 7.6 seconds with profiling. Thus the historical
60-second failure does not reproduce, and no measured speedup over that former
build is claimed. The final production module and the scratch data-identity
probe both compiled successfully. The probe proves that the adjunction and unit
are the archived constructions (heterogeneous equality) and that the explicitly
typed point pullback is the original functor. The default compile limit was not
changed. The final delivery also runs the mandatory single-file/preflight checks.
The equation's axiom print retains the inherited `sorryAx` from the original
left-adjoint theorem; this is not a claim to have eliminated that hole.

Consumer checks: `tools/downstream.py --allow-missing --uses` finds no current
Lean importers or external users; searching the quarantined sources finds these
names only in this item's archive. Nevertheless its DAG parent
`thm-zl-real-mixed-by-curves` and unit descent step still need it, so the module
is restored rather than withdrawn. No consumer adaptation is needed.

## Proved and sorry left

Original theorem holes closed: 0 of 2. Holes added: 0. Split off: 0.

The following existing holes remain, each attached to
`lem-zl-constant-extension-mixed-descent`, with the archive's source and complete
natural-language proof unchanged:

- `WeilConjectures.constantExtensionWeilPull_isLeftAdjoint`.
- `WeilConjectures.constantExtensionMixedDescent`.

`WeilConjectures.constantExtensionWeilPush_eq` is fully proved by unfolding and
reflexivity. All original proved constructions are preserved; no theorem proof
has been replaced by a hole. There is no hole inside a definition. As before,
the right adjoint is selected from a universal property that determines it up to
the adjunction-compatible isomorphism.

## No longer needed

None. No import, module, node or proof dependency is pruned. The two large
transparency overrides are no longer file-wide; their remaining need is scoped
to the existing final theorem statement. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The quarantine's timeout is historical: it is not reproducible on the current
published build. This packet therefore makes a concrete definition/interface
repair rather than submitting the archive byte-for-byte or claiming to have
closed its theorem holes. It uses irreducibility and an explicit defining
equation to control reduction of the choice-based constructions.

Reading the dependency nodes also found that
`lem-zl-power-spectrum-conjugation`, `lem-zl-split-sheet-adjunction`, and
`lem-zl-constant-extension-sheet-weil-action` currently have no Lean attachment.
This does not affect the assigned definition repair. Their source proof steps
are retained; no substitute theorem, new hole or speculative dependency was
introduced. The current blueprint's finite-extension trace argument and the
unit's descent route remain the intended mathematical argument.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
