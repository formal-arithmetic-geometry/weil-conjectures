## What changed

Proved `AlgebraicGeometry.Etale.isIso_abelianBaseChangeMap_of_flat` with its original
signature. The only Lean file delivered is
`lean/Sheaf/AlgebraicGeometry/AbelianDegreeZeroFlatBaseChange.lean`. Its public imports,
existing docstring, definitions and statement are unchanged.

The proof uses `etaleInverseImageAbelianLift_hom` for the inverse-image comparisons along
f and e. Its hom-set equation, applied to an identity, supplies the unit equation for e.
Applying the set adjunction bijection for f reduces comparison of the exchange arrows to
the proved `unit_map_baseChangeMap_app` formula. Direct-image composition has the same
restriction maps after forgetting coefficients, and naturality of its comparison moves
the inverse-image isomorphism through the square. Thus the conjugated underlying map is
exactly `setBaseChangeArrow`, rather than just some isomorphism between its endpoints.
The existing set-valued flat base-change theorem makes it invertible; canceling the
comparison factors and reflecting isomorphisms through `sheafForget` proves the result.

Updated `dag/nodes/sec-smooth-purity/lem-kun-0eys.json` in `proof`, `proof_deps`, and
`proof_origin` to record this route. Removed the two obsolete top-level `tool_uses` entries
for composition-unit uniqueness and square-iso pasting. There is no interface change or
consumer adaptation, so no change record is required. The unit's `realized` record has no
statement or step assigned to this node; the prescribed 0EYS set-valued input is retained.

Validation: the single-file compiler accepted the proof without errors or warnings. The
normal delivery dry run supplies the declaration and axiom probe. The argument is uniform
in F and g, including zero F, identity morphisms and empty schemes/fibres: no nonemptiness,
torsion or extra flatness assumption is introduced.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.isIso_abelianBaseChangeMap_of_flat` (node `lem-kun-0eys`).
Item holes: 1 before, 0 after. Holes added: 0. Split off: 0. No declaration delivered here
contains `sorry`. The proof uses the already stated
`AlgebraicGeometry.isIso_etaleSetDegreeZeroBaseChange_of_flat`; proving that dependency
remains a separate item, as intended by stage 3. This delivery closes the item's hole
without claiming that its whole transitive dependency closure is now axiom-free.

## No longer needed

Removed direct proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
  (`lem-weil-pbc-sets-etale-inverse-image-composition-units`): the pushforward-unit formula
  for the actual exchange avoids comparing inverse-image composition maps by uniqueness.
- `WeilConjectures.SixFunctors.BaseChange.Pasting`
  (`lem-weil-pbc-square-iso-pasting`): no square pasting theorem is used.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: its declarations remain available
  through the original public import of `BaseChange.Square`.

The first two nodes are removed from the direct proof dependencies and their obsolete
`tool_uses` entries are removed, preserving the order of the remaining entries.
`lem-weil-pbc-inverse-image-composition` remains needed for `lowerStarComp`; only its
inverse-image composition clause is unused. The new proof-only import of
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom` provides an existing,
proved, smaller hom-set comparison theorem. No new module or node is introduced. The
removed imports can still be reached through other modules; this is direct pruning and
does not assert that their whole modules have left the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but expands a coherence calculation already
proved as `unit_map_baseChangeMap_app` in the source library. Using that formula avoids
repeating the inverse-image composition-unit and pasting argument. Its only additional
input is the existing hom-set specialization of the original algebraic-structures
comparison. No mathematical statement was corrected or weakened.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
