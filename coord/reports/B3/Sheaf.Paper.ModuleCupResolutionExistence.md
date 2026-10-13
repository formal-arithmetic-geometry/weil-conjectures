## What changed
Added a component-data intermediate theorem with a named sorry, and proved the target by packaging its degree maps with `HomologicalComplex.Hom.mk`.

## Proved and sorry left
Closed `moduleCup_resolution_realization_exists`. Left `moduleCup_component_data_exists` as a decomposition theorem, with node `lem-sc-module-cup-resolution-components`.

## No longer needed
None; the declared realization infrastructure remains needed for the target interface.

## Where the brief, the DAG or earlier work was wrong
The original proof plan omitted the explicit intermediate component-data interface required to package the total coproduct maps as a cochain morphism.

## Earlier second reading (a previous round; superseded)
The target packaging proof was compiled independently; the new component-data statement is strictly the degree-map and chain-equation part of the target and retains the planned unit route.

## New nodes
`lem-sc-module-cup-resolution-components` in the copied DAG node directory.

## Second reading by B3
1. The delivered module was diffed against the repository version. Existing declarations,
including the target theorem, retain byte-for-byte identical signatures; only the new
component-data declaration and proof bodies were added. Verdict: pass.
2. The module compiles with `lcompile.py`; the only remaining `sorry` is the named
`moduleCup_component_data_exists`, and it is documented and represented by its DAG node.
No definitions contain `sorry`, and the realization theorem packages the component maps
with `HomologicalComplex.Hom.mk`. Verdict: pass.
3. The split-off component-data statement is a strict intermediate interface: it gives
degree maps, the section formula, and the chain equation, while omitting the existential
cochain morphism packaging. Its source, proof description, and searches are recorded in
`lem-sc-module-cup-resolution-components`; no duplicate declaration was found in the
library or Mathlib. Verdict: pass.
4. The proof follows the component assembly route and keeps the unit's realization step;
the target's only proof dependency is now the component-data node. No imports or old proof
dependencies were unused, so nothing was pruned. Verdict: pass.
5. The Lean declarations, DAG statements, proof steps, dependencies, and origins agree:
the target node invokes the component theorem and `HomologicalComplex.Hom.mk`, and the new
node records the remaining theorem exactly. Verdict: pass.

Changed only the module proof and the corresponding component-data declaration, its DAG
node, and this report. No statement or definition used by other modules was changed.
