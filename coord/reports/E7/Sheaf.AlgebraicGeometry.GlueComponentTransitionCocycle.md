## What changed

Completed the listed retirement of Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle by withdrawing its unused duplicate theorem and private helpers. Repointed lem-sc-glue-component-transition-cocycle to the existing proved AlgebraicGeometry.exists_invertible_of_cech_transition in WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle. Its proof route and mathematical conclusion are unchanged. The upstream theorem needs only hcoc; the former hid and hinv arguments were explicitly cleared by the retired proof. No source-library file is changed.

Change record: coord/changes/E7-retire-glue-component-transition-cocycle.md.

## Proved and sorry left

This is a zero-hole retirement: 0 original sorries, 0 closed, 0 added, 0 remaining, 0 split off. The existing upstream theorem AlgebraicGeometry.exists_invertible_of_cech_transition is retained in full. A scratch compatibility theorem derives the entire former signature by applying the upstream theorem to U, hcover, g, hcoc. It compiled through lcompile.py in 2.9 seconds; #print axioms reported exactly propext, Classical.choice and Quot.sound. The check is in scratch/lean/Sheaf/AlgebraicGeometry/GlueComponentTransitionCompatibility.lean and is not part of the delivery.

## No longer needed

Pruned Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle, including its private transitionHom, transitionIso, frame_hom_ext and frame_relations. Its removed imports are WeilConjectures.AlgebraicGeometry.Modules.Invertible, WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator and Sheaf.Topology.GlueSheavesOfModules. The two source definition modules and the upstream gluing theorem remain necessary to the retained upstream proof; their DAG nodes are not pruned. No tool_uses approvals are removed. No current module imports the retired Sheaf module, so no consumer adaptation is needed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a sorry item, but coord/retire-items.tsv explicitly assigns this module for retirement and the module already has zero holes. Its node still pointed to the obsolete Sheaf copy and recorded the extra redundant identity and inverse hypotheses. The node now points to the existing upstream theorem, with the same mathematical conclusion and proof route. The inventory historical consumers have already migrated to the source tree. No new nodes are needed. Required msearch.py searches ran: LeanFinder returned eight general sheaf-gluing matches; the exact-name Loogle and grep queries returned zero matches. Direct rg of the project found the exact existing upstream theorem and its three upstream consumers, which is the shortest route.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
