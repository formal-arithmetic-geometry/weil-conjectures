## What changed

Completed the assigned duplicate-path retirement of
`Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`, listed in
`deleted.txt`. The canonical constructions remain in
`WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison`.

Transferred the three existing proved characterization theorems, verbatim, to
`Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso`:
`AlgebraicGeometry.Etale.RawModuleScalarComparison.pullback_unit`,
`AlgebraicGeometry.Etale.RawModuleScalarComparison.eq_pullback_of_unit`, and
`AlgebraicGeometry.Etale.RawModuleScalarComparison.kanSheafification_eq_pullback`.
All receiving-module imports and existing declarations remain unchanged. The
receiving module already publicly imports the canonical upstream twin and retains
the historical scalar-forgetting aliases and instances.

Replaced the retired public import in both current direct consumers,
`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer` and
`Sheaf.Paper.CartierRelativeBoundaryRealization`, with the receiving module.
These are import-only changes; their declarations and proofs are byte-identical
to current shared source. No upstream file or target statement changes.

The canonical DAG node already points upstream. Updated its proof text and Lean
note to locate the retained characterization results and record the retirement.
Change record: `coord/changes/N1-retire-raw-scalar-pullback-import.md`.

## Proved and sorry left

Assigned item: 0 sorries before; 0 after withdrawal. Holes closed: 0 of 0.
Holes added: 0. Split off: 0. This is duplicate-path retirement, not a hole-count
improvement. All three transferred proofs are preserved verbatim and complete.

The only sorry in the delivered Lean files is the unchanged pre-existing theorem
`WeilConjectures.PurityFiniteSetting.cartier_relative_boundary_realization`
(node `lem-pur-cartier-relative-boundary-realization`). Its statement, docstring
and proof are unchanged. The receiving module and OrdinaryFiniteP1Kummer each
have zero sorries. No definition is hollowed and no new statement is introduced.

Full sandbox compilation passed via lcompile.py --all on 2026-10-25, exit code 0:
RawModuleScalarDerivedPullbackIso 16.3 seconds; OrdinaryFiniteP1Kummer 50.6 seconds;
CartierRelativeBoundaryRealization 73.4 seconds. The theorem transfer, unchanged
receiving-module code, import-only consumer changes and 100-column limit were
also checked mechanically. The canonical formulas retain their full generality,
including zero coefficients, empty schemes and identity morphisms.

Current-source checks on resumption confirmed the verbatim theorem transfer,
import-only consumer changes, and absence of any new live or quarantined importer.
Earlier delivery attempts exhausted the capacity wait with exit 75 before
preflight or push; the required delivery is retried on resumption. No launcher
scripts, capacity gates or compile limits were changed.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison`.
Its two remaining import edges are replaced with the receiving module. The
retired module's own import of that same receiving module disappears.

No mathematical construction, theorem, node, dependency or proof step is pruned.
All 21 DAG parents keep their references to the canonical node. Its two declared
proof dependencies, `lem-weil-pbc-constant-module-sheaves-forget-colimits` and
`lem-weil-pbc-module-abelian-inverse-image-comparison`, remain in use upstream.
The unit `sk-lem-failure-field` has no realized attachment to the retired path;
its route is unchanged.

A current scan of lean/ and quarantine/ finds exactly the two direct consumers
adapted in this packet and no archived importer of the retired path. After the
packet overlay, no import of the retired path remains. The other seven consumers
in the retirement inventory already import upstream. The three preserved
characterization lemmas have no external textual users, and remain available
through both migrated public imports.

Both consumers' import closures are exactly their previous closures minus the
retired path, with no added module: OrdinaryFiniteP1Kummer 1253 to 1252 modules,
CartierRelativeBoundaryRealization 12963 to 12962. Hence this migration introduces
no new twin collision. Import-direction checks also pass.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished, repeatedly split obligation.
The current source instead has zero holes in this item and an explicit retirement
assignment. Earlier landings already migrated the canonical data upstream and
retained the old path for quarantined consumers; later work placed the three
proved characterization lemmas there. The remaining Cartier consumer is now live
and can migrate together with OrdinaryFiniteP1Kummer. The three theorems are
retained rather than discarded.

The old node note called the compatibility module declaration-free and referred
to quarantined consumers. The updated note matches the current source. Its
canonical upstream attachment, mathematical statement, dependencies and unit route
stay unchanged.

The earlier attempt's LeanFinder, Loogle and grep searches located adjunction
uniqueness, Equiv.apply_symm_apply and sheafComposeNatTrans_fac. Re-reading the
upstream constructions and existing proofs confirms that no new mathematical
result is needed. Both adapted consumers and the receiving module were checked
against current shared source before this session's initial delivery attempt;
concurrent repairs, including ordinaryFiniteDegreeZero and its instances, are
preserved. The earlier proof-cache experiment stays in scratch/ and is excluded
from the delivery.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
