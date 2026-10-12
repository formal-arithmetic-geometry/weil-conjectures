## What changed
Added `zariskiModuleAbelianCohomologyNatural_components`, a componentwise comparison and naturality intermediate theorem, and assembled it with `NatIso.ofComponents` to prove `zariskiModuleAbelianCohomologyNatural`. The intermediate theorem remains the single documented proof hole.

## Proved and sorry left
`zariskiModuleAbelianCohomologyNatural` is proved. `zariskiModuleAbelianCohomologyNatural_components` remains `sorry` and is recorded in `new-zariski-module-abelian-cohomology-components`.

## No longer needed
No imports were removed; all existing proof imports remain available for the unresolved injective-resolution comparison.

## Where the brief, the DAG or earlier work was wrong
The DAG's full five-step proof requires substantial derived-category glue. The delivery factors the needed result into component isomorphisms plus their naturality, then uses the standard `NatIso.ofComponents` constructor.

## New nodes
`new-zariski-module-abelian-cohomology-components` records the intermediate theorem and its injective-resolution source.

## Earlier second reading (a previous round; superseded)
The component theorem is a strict decomposition: it supplies component isomorphisms and the naturality equation, while the target proof independently assembles them with `NatIso.ofComponents`. The target signature is unchanged.

## Second reading by U3

1. Compared the delivered module with the repository version. The target theorem signature is unchanged; the added declaration is a separately named componentwise statement. Verdict: pass.
2. Compiled the module successfully. The target theorem has no `sorry`; the only remaining `sorry` is the documented `zariskiModuleAbelianCohomologyNatural_components`, with its matching DAG node. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked the split statement against the injective-resolution comparison in Stacks Tag 03FD. It is a true componentwise family with the exact naturality equation needed by `NatIso.ofComponents`, and does not merely restate the target. Verdict: pass.
4. Checked the proof route and imports. The target proof uses the split component theorem and `NatIso.ofComponents`; no proof import was removed because the component theorem's statement requires the existing imported interfaces. Verdict: pass.
5. Checked DAG agreement and the unit route. The target node now records the actual two-step proof and depends on the component node; the unit `sk-prop-cd` route is untouched. Verdict: pass.

Changed the target documentation to retain its original blueprint, recorded the target node's actual proof dependencies, and added this second-reading record.
