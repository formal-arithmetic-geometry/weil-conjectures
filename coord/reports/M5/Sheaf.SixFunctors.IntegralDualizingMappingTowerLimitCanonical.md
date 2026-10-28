## What changed

Replaced the proof hole in
`WeilConjectures.integralDualizing_mapping_tower_limit_canonical`, keeping its
statement and both original public imports unchanged. Added only private proof
imports and proved private helpers in its module. The proof resolves the given
strict tower by a K-injective complex of injective towers, identifies the ordinary
limit complex with the canonical derived limit using its actual derived unit,
and proves that the limit complex is K-injective using the constant/limit
adjunction. It constructs the global-Hom/ordinary-limit comparison naturally in
the source by projecting into the limit. Finally it descends the natural
isomorphism through the opposite derived localization and restricts to the
constructible source category.

Added two modules, `IntegralDualizingResolvedGlobalHom` and
`IntegralDualizingResolvedMappingLimit`, under `Sheaf.SixFunctors`. Their model
functors are actual constructions: signed internal Hom, scalar sections along
the actual constant-to-completion map, constant-ring sequence internal Hom,
and ordinary limits of complexes. No data are selected from an unproved mere
existence theorem. Each module contains one remaining comparison theorem.
Updated the item's proof plan and recorded the two new nodes.

The three files compile individually through lcompile.py. The last main-module
compile took 28 seconds; the two new modules took 12.9 and 9.1 seconds. The
resolved Hom/limit helper has a scoped heartbeat allowance for elaborating the
large section-scalar bifunctor. All delivered Lean lines have at most 100
characters. No other existing module, declaration signature, instance, public
import, target, or unit realization was changed.

## Proved and sorry left

Closed the original body hole of
`WeilConjectures.integralDualizing_mapping_tower_limit_canonical` by a complete
Lean proof from existing declarations and two strictly smaller comparison
statements. There are zero holes in the item module. The private constructions
`evaluatedLimitCone`, `evaluatedLimitIso`, `evaluatedLimitKInjective`,
`resolvedHomLimitIso`, `ambientGlobalHomMapIso`, and
`ambientMappingTowerMapIso` are all proved/constructed without holes.

This is a decomposition, not a net reduction of the sorry count: one existing
hole closed, two holes added, net minus one. Every remaining hole is the entire
body of one named public theorem:

- `WeilConjectures.integralDualizing_resolved_globalHom`, node
  `lem-coef-integral-dualizing-resolved-global-hom`, in
  `Sheaf.SixFunctors.IntegralDualizingResolvedGlobalHom`.
- `WeilConjectures.integralDualizing_resolved_mappingLimit`, node
  `lem-coef-integral-dualizing-resolved-mapping-limit`, in
  `Sheaf.SixFunctors.IntegralDualizingResolvedMappingLimit`.

The first comparison has no tower and no limit. It computes global derived Hom
on a fixed K-injective target by its signed global Hom complex. The second
comparison computes only the mapping-tower side for an already resolved tower
by an ordinary limiting complex. It has no canonical sheaf limit and no
normalized DVR tower. Neither has the same conclusion as the item or merely
repackages its hypotheses. The limit bridge, its source naturality, use of the
canonical derived unit, and derived descent combining these two comparisons
are proved in the item. Their docstrings and nodes include complete prose
proofs and source references. The proposed statements were checked on zero
source and target complexes, the empty scheme, and split-transition towers;
all comparisons respect the prescribed scalar action and signed differentials.

## No longer needed

No original dependency, module, or node is pruned. Both original public imports
remain necessary. The original generic global-RHom derived-limit dependency is
used for its resolved-tower existence clause, and the mapping-tower definition
is still used. A redundant private import of the new fixed-target model module
was removed after compilation: it is already publicly imported by the new
resolved mapping-limit model. There is no remaining unused proof import and no
withdrawal.

## Where the brief, the DAG or earlier work was wrong

No false statement or process defect was found. The generic global-RHom theorem
is parameterized by a fixed derived source; its conclusion is natural in the
strict tower. Applying it alone does not supply the naturality in the varying
constructible source required by this item's functor isomorphism, nor the
identification with the specific integral scalar and constant-ring sequence
models. The proof explicitly constructs source naturality for the limit bridge;
the two new comparisons isolate precisely the remaining model identifications.
No unit route was bypassed.

## New nodes

`lem-coef-integral-dualizing-resolved-global-hom` states the fixed K-injective
target global-Hom comparison. The proof proceeds by terminal-object sections,
the replacement-normalized internal-Hom comparison, and K-flat source
resolution followed by K-injective invariance. It cites Stacks 0B6E, 0A95,
0A96, 08JA, and the existing internal-Hom sections model.

`lem-coef-integral-dualizing-resolved-mapping-limit` states the resolved
constant-ring sequence mapping comparison. It uses the section-preserving
sequence equivalence and its normalized slice formulas, followed by the
ordinary-limit/Roos comparison for split transitions. It cites Stacks 0941,
0A95, 0A96, 08JA, the blueprint's integral-dualizing proof, and the existing
sequence scalar and resolved tower models. Each new node records the actual
Mathlib searches and the exact Lean theorem. No change record is needed:
no existing statement or definition was repaired or changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerLimitCanonical": "2ae9fac33d95b952ebd26062a5c95d0dc9c20b75", "Sheaf.SixFunctors.IntegralDualizingResolvedGlobalHom": "48869cbba04ff3f7640934f140da1ee7c46e13d3", "Sheaf.SixFunctors.IntegralDualizingResolvedMappingLimit": "6c4df763408ff3346ecb77e08e115f9e9b095d31"}, "results": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerLimit": {"hash": "5c902229735853a11f6d1fdc929f65f328224583", "status": "OK"}}, "seconds": 147, "time": "2026-10-28T12:12:00+0800", "transitive": 0, "version": 1}
```

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
