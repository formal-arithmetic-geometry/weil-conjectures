## What changed

Completed `AlgebraicGeometry.Proj.gradedModuleSheaf_stalks` using the explicit prime degree-zero submodule, the canonical stalk map, and the homogeneous annihilator lemma. Added the two lower modules as named intermediate statements with documented statements and updated proof dependencies.

## Proved and sorry left

The target theorem `gradedModuleSheaf_stalks` is proved. The new lemma `homogeneousVectorAnnihilator` is fully proved. One upper hole is closed and one lower hole is added: the decomposition leaves only `AlgebraicGeometry.Proj.gradedModuleStalkMap` (node `lem-weil-pbc-proj-graded-module-stalk-map`). This is a decomposition with net zero holes, not a closed proof of the target import closure.

## No longer needed

Removed the proof import `Sheaf.Topology.PresheafModuleStalkFunctor` (node `def-weil-pbc-module-stalk`): the RingedSpace stalk functor already imported publicly gives the carrier needed here. The proof uses the standard-open properties, stalk map, and homogeneous annihilator modules; The Mathlib basis-germ and ring standard-section dependencies are retained through the canonical map node; no unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had the complete target proof but did not package the lower intermediate nodes or report, so it could not be delivered. The target proof itself compiles unchanged in the sandbox.

## New nodes

`lem-weil-pbc-proj-graded-module-stalk-map` isolates construction and compatibility of the additive map, without bijectivity. Its values on chart germs uniquely determine the map, so the parent does not choose arbitrary unspecified data.

`lem-weil-pbc-homogeneous-vector-annihilator` is the fully proved component argument used in injectivity. It permits negative module degree and zero-degree annihilators. No change records: existing statements and definitions are unchanged.

## Second reading by R2

1. The delivered target module was compared with the repository version. The theorem signature and all existing declarations are unchanged; only proof imports, the explicit construction, and proof bodies changed. Verdict: pass.
2. All delivered modules compile with `lcompile.py --all`. The homogeneous annihilator lemma is fully proved; the stalk-map theorem is an explicitly weaker intermediate statement and retains its documented `sorry`. No definitions contain `sorry`, and no prohibited declarations occur. Verdict: pass.
3. The new intermediate statements are strictly parts of the target proof: the canonical additive stalk map and the homogeneous annihilator component lemma. Both have source documentation and matching DAG nodes; the annihilator statement is proved and the map statement is the sole remaining lower hole. Verdict: pass.
4. The proof follows the unit route through standard-open properties, the canonical stalk map, and homogeneous annihilation. The removed presheaf stalk-functor import is unnecessary because the ringed-space module stalk functor supplies the required carrier. Verdict: pass.
5. DAG proof, proof dependencies, and proof origins match the Lean proof and the report records the decomposition and pruning. Verdict: pass.

Changed during second reading: added this review section only; no Lean or DAG changes were needed.

Additional verification: the complete delivery dry run printed OK and ran the declaration
axiom probes and preflight. New searches used leanfinder for compatible maps on a
neighborhood basis, loogle for `TopCat.Presheaf.stalk`, and grep for stalk/localized-module
combinations. The results supply general stalk infrastructure and affine module-stalk
isomorphisms, rather than this Proj chart-system map. The existing private
`basisModule_stalk_lift` cannot be imported as a public theorem and does not itself supply
the fraction or scalar compatibility. No shorter ready-made theorem was found.
The map's fraction formula determines it uniquely because every chart section has a
power-denominator representative and every stalk element has a chart representative.
The zero module and empty Proj cases are harmless; negative module degrees do not enter
the equal-degree carrier, and the annihilator proof separates integer degrees k+z
without any positivity assumption on z. The original standard-section and basis-germ
proof dependencies remain needed by the lower map node; only the old module-stalk
proof dependency is pruned from the parent proof route.
