## What changed

The target module now proves `RingTheory.dvr_abhyankar_local_map_maximalIdeal`. Its proof uses the two new intermediate modules `Sheaf.RingTheory.DvrUnitRootWeaklyUnramifiedDiagram` and `Sheaf.RingTheory.DvrUniformizerRootCompositumMaximalIdeal`, plus Mathlib faithful-flat descent for ideals. The final descent is proved by mapping the equality to the local unit-root extension and contracting it along the faithfully flat local map.

## Proved and sorry left

The target hole `RingTheory.dvr_abhyankar_local_map_maximalIdeal` is closed. Two strictly lower statements remain as named holes: `RingTheory.dvr_unit_root_weakly_unramified_diagram` (node `lem-sbc-dvr-unit-root-generation`) and `RingTheory.dvr_uniformizer_root_compositum_map_maximalIdeal` (node `lem-sbc-dvr-uniformizer-root-compositum-maximal-ideal`).

## No longer needed

The original target imports were retained where required by its public statement. No proof dependency from the target module was removed; the prior residue-separability route is not imported.

## Where the brief, the DAG or earlier work was wrong

The original five-step proof plan omitted the two concrete local constructions needed to connect Abhyankar's root calculation to the displayed ideal equality. They are split as the two new nodes above; the target proof itself is complete from those statements and standard faithful-flat ideal descent.

## New nodes

`lem-sbc-dvr-unit-root-generation` records the generation/gluing part of the finite unit-root local diagram. `lem-sbc-dvr-uniformizer-root-compositum-maximal-ideal` records the weakly unramified maximal-ideal calculation in the uniformizer-root case.

## Earlier second reading (a previous round; superseded)

The target proof compiles and preserves the original signature. The two added statements are strict lower-level constructions: the local unit-root diagram and the uniformizer-root maximal-ideal calculation.

## Second reading by F4

1. **Interfaces and statements.** Compared the delivered target module with the repository version. The target declaration is byte-for-byte unchanged; the two new declarations have explicit, separately named lower-level statements matching their DAG nodes. Verdict: pass.
2. **Proof and axioms.** Compiled all three sandbox modules with `lcompile.py --all`. The target has no `sorry`; the only remaining holes are the two named split-off theorems. No forbidden commands or hollow definitions occur. Verdict: pass.
3. **Truth and strength of split-offs.** The unit-root theorem states the needed existence and compatibility data, including fraction-field generation; the uniformizer-root theorem states exactly the maximal-ideal equality consumed by the target. Their docstrings give the source and construction argument, and each has a matching node. Verdict: pass, with the two split-offs intentionally open.
4. **Shortest route and imports.** The target uses standard faithful-flat contraction after the two concrete constructions. Its additional flatness imports are proof-only imports, while public imports remain those required by signatures. No prior dependency is unused by the proof. Verdict: pass.
5. **DAG and unit route.** Updated node proof/proof-dependency metadata agrees with the target's calls and the two new modules' declarations. The proof follows the unit's root/normalization route through the stated intermediate constructions. Verdict: pass.

Changed in this second reading: added this required review record; no Lean code or statements required repair.
