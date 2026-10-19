## What changed

Completed all five proofs in `Sheaf.Paper.LocalFrobeniusTrace`. Four proved private helpers compute positive powers on the point, their two geometric-fibre projections, and the universal pullback return equation. The extension-point and closed-point cases then use the existing field-Frobenius fixed-image theorem. The residue degree is positive by the finite residue-field criterion.

Added the proof-only import `WeilConjectures.PointCount` for `Scheme.Hom.specMap_residueFieldAlgebraMap`. Existing public imports, declaration signatures, definitions and docstrings are retained. The elaborator respects transparency by default here; the three Frobenius-specific scheme-map helper proofs locally permit unfolding. A general scheme-map induction computes the projection identities without repeatedly unfolding the geometric-fibre definition. This avoids expensive instance synthesis in the existing coefficient constructions. Updated the existing DAG node to describe these proofs.

## Proved and sorry left

Closed 5 original holes, all attached to `def-weil-local-frobenius-trace`:

- `WeilConjectures.localExtensionPoint_compatible`
- `WeilConjectures.localExtensionPoint_return`
- `WeilConjectures.localClosedPointDegree_pos`
- `WeilConjectures.localClosedPoint_compatible`
- `WeilConjectures.localClosedPoint_return`

Added 0 holes. No `sorry` remains in the delivered module, and no new modules or unproved lemmas are introduced.

## No longer needed

None. All existing imports support the unchanged definitions or the completed proofs. No nodes or modules are pruned. The existing finite-field and residue-field results suffice without additional intermediate theory.

## Where the brief, the DAG or earlier work was wrong

The node previously had an empty proof list although the module contained five proof obligations. These now have a concrete recorded route. The semilinear return equations and all original hypotheses are preserved. No mathematical statement or definition repair is needed.

The dispatcher reset `.budget.start` during provider-error resumptions (observed values 1792423698.1685352 and 1792437874.145777); no budget metadata was edited by the worker. Work continued in the original sandbox throughout.

The interface-visible transparency option is recorded in `coord/changes/local-frobenius-trace-transparency.md`.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
