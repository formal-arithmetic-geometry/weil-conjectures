## What changed

Retired the zero-hole duplicate
Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt in favor of its
proved WeilConjectures twin (retire-items.tsv row 1206). The sole direct consumer,
DeterminantWedgeMorphismLocal, now imports that twin and the existing canonical
exterior-sheaf comparison privately. Its original theorem is proved by composing
the official map with source and target comparison isomorphisms and checking the
wedge formula. Its two public theorem signatures and all public imports are
unchanged. The item node points at the upstream declaration with its exact
signature and proof; the consumer node describes the transport.

Change record: coord/changes/V4-retire-determinant-wedge-morphism-local-at.md.

## Proved and sorry left

Zero holes before, zero holes after: 0 closed, 0 added, 0 split off.
AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_local_data_at remains
proved in the official library. The adapted consumer theorem
AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_local_data has a complete
proof from it and exteriorSheafPowerIso; the existing
AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_of_local_data is unchanged.
The new private exteriorSheafPowerIso_hom_wedge helper is proved. No sorry remains
in any delivered Lean source.

The adapted direct consumer compiled cleanly through lcompile.py in 3.9 seconds.
The import-direction check permits the official import. The delivery preflight
checks the final packet and every declaration's axioms independently.

## No longer needed

Withdrawn module:
Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismLocalAt.
Its consumer removes that proof import and imports the official twin instead.
The old private presheaf comparisons, map and wedge-map transports, and
quotient-factor compatibility proof inside the withdrawn copy are unnecessary:
the official theorem performs the complete construction once, and only the final
morphism needs transport. No adopted source-library declaration is removed.

The item node no longer needs lem-sc-exterior-sheaf-power-comparison; that
comparison remains needed by the legacy consumer. The consumer's stale proof
dependencies def-sc-sheaf-exterior-power and
lem-weil-pbc-exterior-power-free-basis are replaced by its actual uses,
new-local-wedge-at and lem-sc-exterior-sheaf-power-comparison. The exterior-sheaf
definition remains a statement dependency. The official map, wedge-map and quotient
factor nodes remain required by the official theorem. No other module is claimed
as pruned, and no DAG node or determinant-unit step is deleted.

## Where the brief, the DAG or earlier work was wrong

The current assigned file already had no sorry; it is a listed retirement repair.
The official theorem changes the exterior-power representation, so a bare import
rewrite does not preserve the consumer. The explicit comparison transport repairs
that interface without changing its mathematical statement. The consumer node's
old basis-expansion plan did not describe its actual proof; it now cites the
local-at theorem and comparison. Degree zero, rank zero, empty opens and schemes,
and zero rings are covered by those same unconditional comparison identities.
No new statement, hypothesis, axiom or arbitrary data choice is introduced.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
