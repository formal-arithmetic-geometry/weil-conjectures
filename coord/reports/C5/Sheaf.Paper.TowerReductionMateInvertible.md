## What changed

Filled `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_reductionMate_isIso`
in `Sheaf.Paper.TowerReductionMateInvertible`. The ordinary mate is an isomorphism
by the existing variable-power cokernel theorem, exact inverse image, and faithful
forgetting. A private representative calculation identifies the specified derived
mate with the ordinary comparison between the two derived counits. Existing
power-system regular resolutions compute both counits, and naturality transports
the result to every derived object.

Added only private proof helpers and private proof imports; the existing public
statements, definition bodies, universes, exported attributes, and public imports
are unchanged. Local reducibility settings expose the cochain and tower
projections used in the comparison calculation. Updated the item's node proof,
proof dependencies, and proof origin to this route. No other existing module is changed.

Validation: `lcompile.py` compiled the proof cleanly in 23.2 seconds. A temporary
`#print axioms tower_reductionMate_isIso` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`; that diagnostic command was removed before
delivery. Both new Sheaf import directions were checked and have no cycle. The
public mate definition body and theorem signature match the original verbatim.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.tower_reductionMate_isIso`
(`lem-sp-tower-reduction-mate-invertible`). Added no holes and split off no
statements. The delivered module contains zero `sorry` declarations.

## No longer needed

The new proof does not directly use the old planned dependencies
`lem-pur-torsion-sheaf-constant-module` or
`lem-pur-algebra-diagram-pullback-extension-coherence`. In particular it does not
import `Sheaf.CategoryTheory.AlgebraDiagramPullbackExtensionCoherence` or construct
sequence-site realizations and K-flat scalar-extension comparisons. The existing
power-system ordinary cokernel and acyclic resolution modules supply a shorter
route. The torsion-module infrastructure remains a transitive dependency of the
ordinary-cokernel calculation; this delivery does not assert its global
withdrawal. Exact inverse-image infrastructure remains used to preserve
levelwise regularity. No original Lean import was removed and no module was
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged. The DAG's general algebra-diagram extension-coherence
route was unnecessary once the proved prime-power cokernel and regular-resolution
calculations were available. A formal transpose calculation suffices to identify
the canonical mate without any integer-unit or Kummer normalization.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TowerReductionMateInvertible": "06a325a7e45695a3516f80d629aef40d0fd1a432"}, "results": {}, "time": "2026-10-28T00:17:30+0800", "transitive": 0, "version": 1}
```

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
