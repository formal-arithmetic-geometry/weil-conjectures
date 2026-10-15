## What changed

Completed `AlgebraicGeometry.Etale.derivedBaseChangeMap_naturality` by applying the
naturality field of `derivedBaseChangeMap` to `v`, with
`simpa only [Functor.comp_map]` to expose the composed-functor maps. The existing theorem
signature is byte for byte unchanged. The public imports are now
`WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded` (the map and derived functors)
and `Sheaf.AlgebraicGeometry.ChosenCartesianSquare` (the square type). No import is
needed only by the proof. Three unnecessary imports were removed, as listed below.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.derivedBaseChangeMap_naturality`
(node `sbc-lem-bc-naturality`). Added no holes or split-off statements. No `sorry` remains
in the delivered module. A scratch copy compiled with `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for this theorem.

## No longer needed

Removed the public imports `Sheaf.AlgebraicGeometry.DerivedBaseChangeNaturality` and
`Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`, and the plain import
`Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`. The first supplies a different
naturality theorem for ringed-space modules; the second supplies an underived comparison
unused here; the third supplies set and abelian exchange helpers unused by this
module-coefficient statement. This removes dependency edges from this module; it does
not assert that these modules are unreachable from all other targets.

The sole old `proof_deps` node, `sbc-def-base-change-map`, is retained: its `lean.declarations`
includes the exact upstream `AlgebraicGeometry.Etale.derivedBaseChangeMap` used here.
Its helper module `BaseChangeMapAbelianAndSets` is unnecessary because the original map
is imported directly from `DerivedUnbounded`. No old proof-dependency node is pruned.
The statement dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

The expanded mate calculation is unnecessary: `derivedBaseChangeMap` is already a
natural transformation, so its `.naturality` field gives the required equality after
simplifying composed-functor maps. The first worker's empty `proof_deps` and claim that
the imported nodes were unnecessary overlooked the retained recorded base-change map.
The first report also omitted the removed plain import `BaseChangeMapAbelianAndSets`.

## Second reading by C1

1. Compared the entire delivered Lean file with the repository version. There is one
   existing theorem and no definition. Its signature, from `theorem` through the
   conclusion before `:= by`, is byte for byte identical. Changes are imports, module
   comment wrapping, and the proof. No target statement or data construction changed.
2. Compiled the module locally through `lcompile.py` without errors or warnings. Scanned
   it for holes and forbidden declarations; none occur. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.Etale.derivedBaseChangeMap_naturality`: only
   `propext`, `Classical.choice`, and `Quot.sound`. The upstream map is constructed as a
   mate natural transformation, and the proof applies its naturality field directly.
3. No statement was split off and no node added. Independently queried Loogle for
   `CategoryTheory.NatTrans.naturality`, and searched the upstream base-change modules
   and the project's derived-base-change modules. The generic field exactly supplies
   this equation. The underived and bounded-below results concern different maps.
4. The direct field application is the shortest route and leaves no local hole. Both
   remaining public imports provide objects in the theorem signature. All three removed
   imports are listed above. Read `dag/units/sk-def-bc.json`: its proof steps and
   `realized.statement`/`realized.steps` are empty, and its statement defines the recorded
   base-change property. This node-level simplification bypasses no realized unit step
   and keeps the recorded base-change map. Naturality applies to every morphism, so
   identity and zero morphisms, zero complexes, empty schemes, and unbounded complexes
   require no extra hypotheses.
5. Compared the delivered node with the repository node. Its statement, statement
   dependencies, Lean attachment, blueprint, unit, and all unrelated fields are
   unchanged. Its proof now records the direct naturality application and its origin
   names the upstream definition. Restored `sbc-def-base-change-map` in the step's
   `uses` and `proof_deps`, since this recorded declaration is used. Their union agrees.

Second reading changed the DAG dependency accounting, completed the pruning and
hole-count report, and added the public-import change record required by the dry run. The Lean proof needed no repair. No definition or signature changed;
the public-import pruning is recorded in
`coord/changes/derivedBaseChangeMap_naturality-import-pruning.md`.
