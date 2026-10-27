## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.scalar_p2_chern_splitting` by reducing it to a
componentwise homology criterion and a complete categorical proof that a two-degree biproduct
map is invertible when its two component homology maps are invertible. Added the lower-level
module `Sheaf.Paper.RationalP1ScalarChernP2HomologyCriterion`, whose single geometric theorem
records the transported scalar P2 component maps and their homological concentration.
The item proof imports that module and the additive biproduct lemmas needed for the categorical
argument. The target statement and all existing definitions are unchanged.

## Proved and sorry left

Closed the `scalar_p2_chern_splitting` sorry. The new theorem
`scalar_p2_chern_homology_criterion` remains `sorry`; it is the strictly lower-level
component concentration and component-isomorphism step, with node
`lem-sfb-rational-p1-scalar-p2-homology-criterion`. No definition contains `sorry`.

## No longer needed

The item proof does not directly use `lem-sfb-diagonal-trace-twisted-splitting-components`;
it is retained as a dependency of the new homology criterion's planned proof. No existing
module or declaration was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The published proof plan describes the geometric transport from the completed diagonal-tower
splitting but supplies no Lean declaration for the resulting scalar P2 homology components.
The missing geometric step is therefore recorded as a separate theorem. The final item proof
is complete from that lower-level statement and proves the remaining categorical assembly
explicitly.

## New nodes

`lem-sfb-rational-p1-scalar-p2-homology-criterion` records the homology concentration of the
unit, shifted line, and second-projection pushforward together with the two component map
isomorphisms. Its Lean declaration is
`AlgebraicGeometry.ProEtale.RationalP1.scalar_p2_chern_homology_criterion` in
`lean/Sheaf/Paper/RationalP1ScalarChernP2HomologyCriterion.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernP2HomologyCriterion": "598144f0379f7d33ce5d022dd006c0d58caae085", "Sheaf.Paper.RationalP1ScalarChernP2Splitting": "23f89058e1310547bf527b4573fd1075ba85290f"}, "results": {"Sheaf.Paper.RationalP1ScalarChernSplittings": {"hash": "cb8089e862807e3e960ab382934c4b655948d9e8", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T04:11:17+0800", "transitive": 0, "version": 1}
```

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
