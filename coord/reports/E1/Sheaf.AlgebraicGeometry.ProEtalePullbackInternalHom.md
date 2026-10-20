## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ProEtalePullbackInternalHom.lean` from its
quarantine archive, retaining its complete existing proof. Changed its private
`import all` to the existing Sheaf.UpstreamExtra home of the moved tensor
comparison helpers. Omitted the unused ambient MonoidalPreadditive assumption
from the private `concreteIhomIso_embedding` lemma. Every public declaration,
public import, and the existing DAG attachment is preserved.

The source-library, Mathlib, and semantic searches found the existing ambient
weakly-etale comparison and module equalizer comparison used by the archived
proof; no shorter replacement is needed for this API repair. The original
three-step DAG proof and its proof dependencies remain accurate.

Change record: `coord/changes/E1-proetale-internal-hom-private-import.md`.

## Proved and sorry left

This is a zero-hole rework assignment. The archive already proves
`AlgebraicGeometry.ProEtale.CondensedRing.supportPullback_ihomComparison_isIso`
and constructs the `supportPullback_monoidal` instance. Their existing proofs
now compile against the relocated helper declarations.

Holes closed: 0 of 0. Holes added: 0. Split off: 0. No declaration in the
restored module contains sorry. Imported unfinished theory is unchanged.

The restored file compiles through lcompile.py without errors or warnings.
The public-signature comparison against the archive reports no changes.
The downstream tool with --allow-missing reports zero live importers. Searching
the quarantine finds ProEtaleFiniteProjectiveDualizable as the direct importer,
using precisely the unchanged public comparison theorem; ClosedSupportStratumHom
is its indirect consumer. Their interfaces need no adaptation. The delivery dry run passed compilation, the axiom probe, and stage-3
preflight (dry-run commit 46095ae0a03; review class CODEX).

## No longer needed

None. The old private import-all path is replaced with the relocated helper's
path; this is not pruning a mathematical dependency. All archived public imports,
DAG dependencies, and consumer modules remain. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assignment is restoration of an already proved, zero-hole quarantined module,
not an unfinished mathematical reduction. The recorded unknown-constant error
comes from private declarations moved by the upstream-verbatim sync. Opening the
existing Sheaf.UpstreamExtra module's private declarations repairs that error.
No mathematical statement, source construction, or unit route was wrong or changed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
