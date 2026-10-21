## What changed

Restored `lean/Sheaf/AlgebraicGeometry/FiniteConstantLocalModel.lean` verbatim from
`quarantine/Sheaf/AlgebraicGeometry/FiniteConstantLocalModel.lean`, as required by
its entry in `coord/rework.tsv` (cluster restore after upstream sync).
The archive contains a complete proof: its scalar-ring construction, scalar extension,
coverwise matrix equivalence, implication to local finite presentation, and explicit
2-adic counterexample are all preserved. This restores the actual missing module,
not an empty replacement or a deletion. No declaration, attribute, import, or proof
in the archived module was changed. The existing node attachment and every dependency
of `det-def-sfb-constructible-local-model` are preserved.

The restored file compiled cleanly through `lcompile.py` against the current server
library in 19.0 seconds. The dependency-cluster failure responsible for quarantine
is not reproduced on the current library. The source-library boundary is untouched.

The blueprint statement and all three proof paragraphs were read, together with the
unit record and the existing seven-step DAG proof. The archive implements the
finite-free comparison and cokernel calculation on the same cover; it does not impose
uniform ranks, nonempty covers, flatness, or extra coefficient hypotheses on those
statements. The counterexample specializes coefficients only to refute the universal
converse. No data is introduced by a new choice from an unproved existence theorem.

## Proved and sorry left

This is a zero-hole quarantine restoration, not new proof progress.
Original archived holes: 0. Holes closed: 0. Holes added: 0. Holes left: 0.
No theorem is split off. In particular the restored existing proofs include
`scalarRingObj_comm`, `scalarConstant_iso_constantSheaf`,
`scalarCoefficientHom_isMonHom`, `scalarConstant_comm`,
`finiteConstantLocalModelOnCover_iff_scalarMatrix`,
`finiteConstantLocalModel_iff_exists_cover`,
`HasFiniteConstantLocalModel.isLocallyFinitelyPresented`, and
`not_locallyFinitelyPresented_implies_finiteConstantLocalModel`
in namespace `AlgebraicGeometry.ProEtale`.

## No longer needed

None. No import, node, module, declaration, or dependency is withdrawn.
There are no live direct importers, but ten quarantined direct importers remain;
absence of live importers is not grounds to withdraw this item.
The existing DAG proof and unit route still require its statement.
Mathlib searches through msearch.py found the existing cokernel preservation API
and sheaf finite-presentation notions, but no replacement for the scalar-matrix
local-model equivalence or the explicit converse counterexample. No duplicate
statement or new module is introduced.

## Where the brief, the DAG or earlier work was wrong

The general brief describes an item with a hole or an assigned repair. Here the
specific rework row assigns restoration of a quarantined module whose archived
proof already has zero holes. The current dependency interfaces suffice without
editing the archived proof. The quarantine archive is retained, and the Lean
attachment and dependencies are not removed. No mathematical statement or definition
repair was necessary, and no new holes are claimed as closed.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
