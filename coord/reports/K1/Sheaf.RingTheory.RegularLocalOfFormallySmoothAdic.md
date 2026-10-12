## What changed

Added `Sheaf.RingTheory.FormallySmoothAdicPowerSeriesMap` with the comparison-map construction as a named lower theorem. The target proof now uses completion, the comparison map, power-series regularity, surjectivity, and the regular-local criterion. Removed two direct imports whose declarations are now used only by the lower theorem.

## Proved and sorry left

Closed hole: `Algebra.isRegularLocalRing_of_formallySmoothAdic` (node
`lem-weil-pbc-fs-adic-field-regular-local`), by a real reduction through completion,
the comparison map, complete-source surjectivity and Krull dimension.
Added hole: `Algebra.exists_powerSeries_comparison_of_formallySmoothAdic` (node
`lem-weil-pbc-fs-adic-power-series-comparison-map`), exactly `:= by sorry` in its
new module. No other holes were added or closed. This is a decomposition: one
upper hole closed and one lower hole added, net zero for these declarations;
the target still depends on `sorryAx`. It is not an axiom-free proof of regularity.

## No longer needed

Removed direct imports `Sheaf.RingTheory.ExistsCoefficientSubring` and
`Sheaf.RingTheory.ExistsLiftOfFieldCharP` from the target module.

Every old direct proof dependency omitted from the target's new `proof_deps`:
- `lem-weil-pbc-char-zero-field-extension-formally-smooth`;
- `lem-weil-pbc-field-char-p-nilpotent-lifting`;
- `lem-weil-pbc-cohen-coefficient-ring-exists`;
- `lem-weil-pbc-nakayama-local-generators`;
- `lem-weil-pbc-noetherian-local-dimension-le-generators`.

The first four remain part of the new comparison-map node's plan. The last is
provided internally by Mathlib's regular-local criterion, rather than used as
a separate declaration here. These are removals from the target's direct
argument, not a claim that the modules have left the targets' whole import
closure. No whole-module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan combines construction of the comparison map with the dimension argument. Splitting that construction gives a usable lower statement while preserving the Tag 07EI route.

## New nodes

`lem-weil-pbc-fs-adic-power-series-comparison-map` is stated in `lean/Sheaf/RingTheory/FormallySmoothAdicPowerSeriesMap.lean` and its proof is left for a subsequent worker.


## Second reading by K1

1. Compared the only modified existing module against the repository with `diff`:
   its existing theorem signature is byte-for-byte unchanged; there are no
   changed definitions, target statements or unreported statement changes.
   The other delivered module and node are new. Verdict: pass.
2. Compiled both delivered modules in import order using `lcompile.py --all`:
   no errors or warnings. The only delivered `sorry` is the named comparison
   theorem reported above. No definitions or forbidden declarations were added.
   Scratch `#print axioms` checks are recorded below. Verdict: pass, conditional
   on the named open comparison theorem and already open dependencies.
3. Read the comparison theorem and its entire natural-language proof against
   [Stacks Tag 07EI](https://stacks.math.columbia.edu/tag/07EI). It isolates the
   construction and tangent-map step, without surjectivity of the map or a
   dimension conclusion. Both conclusion conjuncts are used by the upper proof.
   Checked dimension zero (A a field: the residue map into the zero-variable
   series ring), positive characteristic, and nontrivial residue extensions;
   the prime-field reduction avoids requiring a k-linear coefficient section.
   A dual-number ring would fail the tangent-map lifting and does not satisfy
   formal smoothness, so it is not a counterexample. Repeated LeanFinder,
   Loogle and grep searches with infinitesimal-lifting/tangent-space terminology,
   and searched the project and upstream sources. The closest Mathlib result
   is `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete`; it assumes
   ordinary formal smoothness and a starting map, so does not close this hole.
   The new node has the matching signature, source and complete proof docstring.
   No quick proof of this construction was found. Verdict: valid decomposition.
4. Read the proof top downward. The completion and power-series ingredients are
   existing planned declarations; surjectivity, dimension monotonicity and the
   final criterion use Mathlib. Imports contain no proof-only public import.
   Completed the list of omitted old direct DAG dependencies; no whole-module
   pruning is claimed. Read `dag/units/sk-thm-p1.json` and its `realized` route:
   this is a below-unit reduction and bypasses no unit statement or step.
   Verdict: pass.
5. Checked both nodes against the Lean declarations. Repaired the target's
   proof description to name the actual Mathlib surjectivity and regular-local
   criteria, and retained the formal-smoothness, power-series and regularity
   definition nodes in its dependency list. The comparison node describes the
   construction still left open, with correct source and Lean record.
   Verdict: pass.

Second reading changed only the report and the existing node's proof metadata:
explicit decomposition/hole accounting, complete direct-dependency removal list,
and accurate Mathlib criterion description. The Lean proof itself was correct
and was not rewritten. There are no change records because no existing statement
or definition was changed.
