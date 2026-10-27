## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.CondensedRing.compactSupportRefinement_baseChange`
by a component proof combining two source steps. The proof first uses separated-target
uniqueness from the dense source `w` to identify the refinement composites. It then expands
rho and beta, pastes the proper triangle, applies mate naturality, and applies the local
open-adjunction equation inside the final proper pushforward. The original theorem's
signature and public import are unchanged. Three private proved component formulas avoid
unfolding the full derived constructions during the component calculation. A private
proved calculation for arbitrary categories combines the proper-pasting and
mate-naturality equations; a second calculation applies the local-open equation.
The proper mate stays an explicit parameter during the component calculation, and a
proved wrapper supplies its specified canonical value.

Added `Sheaf.SixFunctors.CompactSupportProperTriangle` and
`Sheaf.SixFunctors.CompactSupportOpenRefinementPasting`. The first separates the general
proper-pasting calculation, for arbitrary derived objects and an arbitrary arrow, with no
opens or compactifications. Its triangle compositor and pulled-back Cartesian square are
actual constructions with complete proofs. The second states the equation on the
compactification before applying the final proper direct image, without density hypotheses.
Neither new statement is the delivered compact-support equation under another name.
The proper step accepts a mate parameter with an equality fixing it to the canonical
proper map; the original theorem supplies reflexivity, adding no target hypothesis.

Changed `detSfCompactSupport` in `Sheaf.SixFunctors.DetSfCompBaseChangeDefs` from `def`
to `abbrev`, retaining its entire type and body. This normalizes the compact-support object
before a derived functor is applied to it. The defining module and its other two direct
importers were unclaimed on the server; their mathematical declarations are unchanged.

The full sandbox compiled in import order. The item took 30.4 seconds; the existing
DetSfCompCompositionBaseChange importer took 21.9 seconds and IntegralCompactSupportDefs
also passed unchanged (24.0 seconds on its first check). The new proper/local modules
passed in 6.3 and 25.5 seconds. All are below the 60-second limit. Profiling options and
temporary unchanged consumer copies were removed before delivery.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.compactSupportRefinement_baseChange`
(node `lem-sfb-compact-support-refinement-base-change`) by decomposition.
The item has zero remaining holes. Added two named theorem holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.compactSupportProperTriangle_pasting`
  (`lem-sfb-compact-support-proper-triangle`).
- `AlgebraicGeometry.ProEtale.CondensedRing.compactSupportOpenRefinement_pasting`
  (`lem-sfb-compact-support-open-refinement-pasting`).

Thus one original hole is closed and two lower holes are added; this is a decomposition,
not a net reduction in holes. The density argument and the combination of the two lower
identities are proved in Lean. Every added definition has real data and no hole.

## No longer needed

No imports, modules or nodes are pruned. The original normalization, refinement-coherence,
identity-open and mate-pasting dependencies remain on the route below the two new steps.
The item now directly uses the two smaller steps and dense-refinement uniqueness.

## Where the brief, the DAG or earlier work was wrong

The current server queue labels the item as a one-hole proof task. The retained rework row
and archived build error refer to an old dependency-import failure. That failure no longer
reproduces: the unchanged item compiled against the published build before editing.

The existing `baseChangeIdentityOpenRestriction` declaration requires arithmetic,
admissibility and finite-type data absent from the item's arbitrary condensed-ring
signature. It therefore cannot directly close the required local equation. The new local
step retains the item's generality and records the direct unit/counit calculation that the
source argument needs. No hypotheses have been added to the assigned theorem.

Kernel profiling exposed expensive conversion of compact-support object aliases beneath
the derived pullback. The abbreviation change retains the actual functor, and the
component calculation keeps the proper mate abstract until its final specialization.

The unit and chapter route is unchanged. In particular, the argument assumes no density
of either base-changed compactification and inverts neither a proper mate nor a refinement
map.

## New nodes

`lem-sfb-compact-support-proper-triangle` is the general proper-mate triangle calculation
and naturality in an arbitrary arrow, with normalized direct-image composition. It is
source proof (3), the application of the final proper pushforward. The node also records
the explicit triangle compositor, pullback map and Cartesian realization used in its type.

`lem-sfb-compact-support-open-refinement-pasting` is source proof (3)'s equality of the two
local maps before applying the final proper direct image. Open-adjunction injectivity and
the canonical restriction normalization give its natural-language proof. Its hypotheses
include equality of the two refinement composites, proved separately in the item.

LeanSearch, Loogle, Lean Finder and Mathlib/source grep found general mate-pasting tools,
not either specialized equation. Both nodes carry the exact Lean statement, source,
proof steps, searches, and the unchanged unit/chapter. The additional existing-module change is recorded in
`coord/changes/K1-compact-support-alias-reducibility.md`. No consumer proof is adapted.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctors.CompactSupportOpenRefinementPasting": "c683a550bdb1c8c4530416e57706199988320024", "Sheaf.SixFunctors.CompactSupportProperTriangle": "c496e140a0e64e1ee3849b51ae115e02314ea717", "Sheaf.SixFunctors.CompactSupportRefinementBaseChange": "b0050269fdfb1cde4c87342b2be592b147090ebe", "Sheaf.SixFunctors.DetSfCompBaseChangeDefs": "d4ab41e95aaf36f78bf00e739d43957950c0202f"}, "results": {"Sheaf.SixFunctors.DetSfCompCompositionBaseChange": {"hash": "fc62f18c40fac2b827b60e8c0c2050614e50d192", "status": "OK"}, "Sheaf.SixFunctors.IntegralCompactSupportDefs": {"hash": "366a803773f3cf75606ed2c9c4352566f44db0fd", "status": "OK"}}, "seconds": 103, "time": "2026-10-28T01:49:47+0800", "transitive": 0, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
