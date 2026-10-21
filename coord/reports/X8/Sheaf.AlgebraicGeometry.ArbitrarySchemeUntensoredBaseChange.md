## What changed

Restore `lean/Sheaf/AlgebraicGeometry/ArbitrarySchemeUntensoredBaseChange.lean` from
the archive named in `coord/rework.tsv`. The archive contains a complete proof,
including its four private helpers. Preserve its public theorem, public imports,
coefficient ring, canonical exchange morphism, and all hypotheses. Preserve the
archive and the existing DAG attachment and dependencies.

The proof first shows that the underlying abelian sheaf of prime-field modules
has stalks killed by the invertible prime. Coefficient forgetting and
`abelian_affineScheme_untensored_baseChange` give the affine case. Pulling back
the affine cover gives jointly surjective etale maps, and the proved source
library etale-locality theorem assembles the local exchanges. The single-object
comparison and identity inverse-image isomorphism identify the local inputs.

Validation: `lcompile.py` compiled the restored module with exit code 0, no
Lean diagnostics, in 23.7 seconds. The server supplied the restored affine
abelian dependency from the current published-source overlay.

## Proved and sorry left

This is a quarantined-module restoration with zero original holes. The archive
has zero `sorry`; the restored module has zero `sorry`. Holes closed: none.
Holes added: none. Split-off theorems: none.

The restored public theorem is
`AlgebraicGeometry.Etale.arbitraryScheme_untensored_baseChange`
(`lem-kun-0f1j-arbitrary-scheme-untensored-base-change`). Its four private helpers
are `prime_module_killed`, `prime_coefficients_killed`,
`prime_coefficients_orders`, and `affineScheme_prime_baseChange`, all proved.

## No longer needed

None. Keep every existing dependency and import. The quarantined parent
`Sheaf.AlgebraicGeometry.PunctualTensorBaseChange` still needs the theorem, and
`lem-kun-0f1j` cites its node in its proof and proof dependencies. No withdrawal
or bypass of the unit route is proposed.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it was quarantined during the upstream
cluster restoration, not because its mathematics was withdrawn. Its archived
proof already has zero holes; this delivery restores the declaration and checks
compatibility with the current dependencies. The abelian affine dependency was
restored in the shared source during this session. No new statement or data
definition is introduced, and no target statement changes.

The restoration and consumer audit are recorded in
`coord/changes/X8-restore-arbitrary-scheme-untensored-base-change.md`.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
