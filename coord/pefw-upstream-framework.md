# Pro-etale module-object framework, 2026-10-15

The upstream import closure was recomputed from bundle ref `up-slop-now`, commit
`c2663dd4d3e221013183c95d20efebe79757eb3e`, in `/tmp/upstream-pefw-scratch` on the
Weil server. Its 18 `WeilConjectures.SixFunctors.ProEtale.ModuleObject.*` roots
reach 432 project modules. Compared with the live library, 51 modules (11,557
upstream lines) were absent. All 51 were copied to `~/weil-newtargets/lean`.

47 files remain byte-identical. Four require compatibility adaptations for the
older live dependencies. No existing live module was replaced in the side overlay:
the affected dependencies have live proof importers. All upstream sorries remain
open; no sorry was filled or added. The launcher's 15 files containing the word
`sorry` include a documentation-only hit in `ModuleObject/UpperLowerStar/Monoidal.lean`.
Lexing the code finds 36 sorry terms in 14 files, unchanged from upstream.

The framework and the attachment-tool support were committed on the side as
`fbd7a31accdb4eb9a415974cc11b539e89888915`. The commit includes only 51 sources,
the source/compile manifest, the new stage-2 attachment helper and promoter, and
the dispatch hunk in `attach.py`. Other sessions' pending changes were preserved.

## Every file requiring more than a copy

Paths below are relative to `lean/WeilConjectures/SixFunctors/ProEtale/`.

| Copied file | Adaptation |
|---|---|
| `FiniteCoefficient/UpperLowerStar/Coherence.lean` | Rewrite the reflexive pullback-congruence case using the live `pullbackCongr_refl` API; the upstream `_left_snd` simp lemma is absent. |
| `ModuleObject/UpperLowerStar/Monoidal.lean` | Supply the upstream pro-etale sheaf symmetric-category and tensor finite-colimit instances where the new module-object framework first needs them. |
| `ModuleObject/Derived/UpperLowerStar.lean` | Include the additive upstream K-flat-preservation and derived-composition declarations, with their original proofs, from `LeftDerivedFunctor/MapDerivedCategory.lean`. |
| `ModuleObject/Derived/BoundedConstructible.lean` | Include the upstream `HasCompactification.of_isOver` theorem and proof from `NagataCompactification.lean`. |

The protected existing dependencies are `MorphismProperty/OverAdjunction.lean`,
`GrothendieckAbelian/Monoidal/Defs.lean`, its `TensorColimits.lean`,
`DerivedCategory/LeftDerivedFunctor/MapDerivedCategory.lean`, and
`Compactification/NagataCompactification.lean`. Direct live importers and all four
patches are retained in the evidence. The two target theorem statements and the
base-change transformation definition are unchanged.

## Compilation and declaration audit

All 51 sources passed `tools/nt_compile.py --json` in import order, with nice 19,
two Lean threads and a hard 60-second timeout for each file. The first complete
framework pass had a maximum of 45.6 seconds (`Colimit/Compatibility.lean`). The
final pass, including the successful audit, had a framework maximum of 44.9 seconds.
There was no `lake build`, global build, or live build request.

The full-library `sorry_map.lean` probe exceeded the same 60-second limit. The
attachment audit instead starts from the checked declarations and recursively
records their project dependencies, stopping at declarations containing sorry.
It uses the compiler environment, source module/range metadata and actual terms;
it does not infer proof closure from successful compilation. The focused probe
passed in 41.0 seconds and emitted 2,746 records covering all 26 selected
declarations. Every project dependency of each inspected sorry-free term is
present. `#print axioms` also confirms `sorryAx` in both targets and the two-colimit
theorem.

## Checked statement matches

All four checked matches were attached through `attach.py --stage2` and promoted
through `nt_promote_attach.py`. The new explicit stage-2 mode accepts reviewed
splits with open proofs, takes a compiler-produced map, and preserves the actual
sorry state. The existing stage-1 closed-proof attachment path is unchanged.

| Node | Primary declaration | Audit | Side commit | Live DAG commit |
|---|---|---|---|---|
| `nt-target-proetale-e` | `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper` | `sorry_here` | `a397af74871b` | `c50f59b640a1` |
| `nt-target-proetale-qbar` | `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl` | `sorry_here` | `6aeb350438b8` | `d71e140d9c97` |
| `def-weil-pbc-condensed-e-module-category` | `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleBaseChange`, plus 22 supporting definitions | `rests_on_sorry` | `8af90828ba96` | `761bd1306dbd` |
| `prop-weil-pbc-qbar-condensed-two-colimit` | `AlgebraicGeometry.ProEtale.constructibleCocone_isFilteredTwoColimit` | `rests_on_sorry` | `599c9c82f00a` | `98e8431fc44b` |

Both the side and live records were checked after each promotion. The full
declaration lists, statement checks and open dependency frontiers are in
[attachment-results.json](../local/pefw/attachment-results.json).

The category definition was checked throughout: continuous functions on profinite
sets; `Spec LC(S,Z)`; left Kan extension and sheafification; scheme inverse image;
internal modules; local finite presentations on finite strata; bounded cohomology;
coefficient transport; derived/restricted operations and adjunctions; and the
unit/square/counit definition of the base-change map.

The two-colimit match uses finite-subextension-valued continuous functions, not
all continuous functions into the algebraic closure. Its hypotheses and the
object/every-morphism/eventual-equality clauses agree with the DAG statement.

`prop-weil-pbc-qbar-condensed-basechange-compatibility` is not attached: the
upstream `Colimit/TwoColimit.lean` explicitly says compatibility of base-change
maps with scalar extension is not yet formalized. Integral-to-condensed
realization, local triviality, recollement and continuity nodes likewise have no
complete matching upstream declaration. The finite-coefficient files reorganize
declarations already present in the live library; their names alone do not
constitute new statement matches.

## Isolation and coordination

Only DAG declaration/audit fields are promoted to the live project. Every task commit
uses Bin Wu <844524296@qq.com>, `SHEAF_LEAD=L-only`, the side merge lock and the
requested co-author trailer; live promotions additionally take the live lock.
No other session's processes were stopped.

The manifest records every copied path and both upstream/side SHA-256 hashes.
The final boundary check verifies that all 51 copied modules are still absent
from the live library, the guarded existing live files and configuration retain
their hashes, and this task's live commits touch only the four intended DAG JSON
files. Concurrent stage-3 and stage-2 work is outside that unchanged-file claim.

## Queue enabled

Enable commit: `9a4649ff317d88cb03323170b848f7bd14d6e155`.

`SHEAF_STAGE2_SKIP_TARGETS` is empty. The broad proetale/pro-etale name filter is removed from `tools/nt_stage2.py`; only explicitly configured target exclusions remain.

Queue snapshot after enabling:

```text
stage 1: 0 nodes to split
stage 2: 351 nodes to state; not open: 93 below a finished node, not needed, 310 waits for a statement dependency
stage 3: not open (lean/TargetsCheck.lean imports no target module yet)
```

Stage-3 boundaries and attachment records were checked at 2026-10-15T05:43:57.424261+00:00. The concurrent stage-2 session continues normally.

Evidence: [source/compile manifest](../local/pefw/manifest-final.json), [final compile log](../local/pefw/compile-final.log), [focused audit metadata](../local/pefw/audit-metadata.json), [attachment commits and frontiers](../local/pefw/attachment-results.json), [live boundary check](../local/pefw/live-boundary-final.json), [all task commits](../local/pefw/task-commits.json), and [sorry preservation](../local/pefw/sorry-preservation.json).

## All copied files

Paths are relative to the side project’s `lean/` directory.

| Path | Result |
|---|---|
| `WeilConjectures/CategoryTheory/FilteredTwoColimit.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/Abelian.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/Bimod.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/ChangeOfScalarsSquare.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/DerivedCategory.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/DerivedExtendScalars.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/ExtendScalars.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/Free.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/GrothendieckAbelian.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/MapMod.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/Monoidal.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/Preadditive.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/ProjectionFormula.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/ModuleObjects/Symmetric.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/RingObjects/Condensed/ContinuousMap.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/RingObjects/Condensed/EllAdic.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/RingObjects/Condensed/FiniteSubextension.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/RingObjects/ContinuousMap.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/RingObjects/EllAdic.lean` | byte-identical |
| `WeilConjectures/CategoryTheory/RingObjects/RingPresheaf.lean` | byte-identical |
| `WeilConjectures/Compactification/Over.lean` | byte-identical |
| `WeilConjectures/ConstructibleSheaf/ProEtaleModule/Def.lean` | byte-identical |
| `WeilConjectures/ConstructibleSheaf/ProEtaleModule/DerivedCategory.lean` | byte-identical |
| `WeilConjectures/Mathlib/Algebra/Category/Ring/Limits.lean` | byte-identical |
| `WeilConjectures/Mathlib/CategoryTheory/Functor/SquareTransport.lean` | byte-identical |
| `WeilConjectures/Mathlib/CategoryTheory/Monoidal/Mon.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/LowerShriek/Defs.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/LowerShriek/Open/Defs.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Coherence.lean` | adapted |
| `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/CoherenceLegacy.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Iso.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Monoidal.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/CompactSupport.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/LowerShriekDefs.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/MorphismDefs.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/Proper.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean` | adapted |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Hom.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/LowerShriek.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/OpenImmersionLowerShriek.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Tensor.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperLowerStar.lean` | adapted |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperShriek.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/LowerShriek/Defs.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/UpperLowerStar/Defs.lean` | byte-identical |
| `WeilConjectures/SixFunctors/ProEtale/ModuleObject/UpperLowerStar/Monoidal.lean` | adapted |
