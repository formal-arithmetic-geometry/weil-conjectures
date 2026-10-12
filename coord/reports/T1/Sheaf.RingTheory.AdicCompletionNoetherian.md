## What changed

Replaced the sole sorry in `lean/Sheaf/RingTheory/AdicCompletionNoetherian.lean`,
`AdicCompletion.isNoetherianRing`, with the four steps of the existing node's proof.
The statement and both public imports are unchanged. Added the proof-only import
`Mathlib.RingTheory.MvPowerSeries.Equiv` for its Noetherian power-series instance.

`IsNoetherian.noetherian I` and
`Submodule.fg_iff_exists_fin_generating_family` produce `n`, `f : Fin n → A`,
and `span A (Set.range f) = I`. The reversed equality is definitionally the ideal
span equality required by `MvPowerSeries.exists_surjective_toAdicCompletion`.
Destructuring that result supplies a ring homomorphism and its surjectivity.
`isNoetherianRing_of_surjective` then applies to the source ring, whose Noetherian
instance is `MvPowerSeries.isNoetherianRing` from Mathlib. All four original proof
steps and all six proof dependencies are retained, so no node update is needed.

The source's second proof was read at https://stacks.math.columbia.edu/tag/0316
(the local literature checkout is absent on this machine). The argument follows
that proof. The unit record `dag/units/sk-thm-p1.json` was read; its realized
statements and steps are unaffected.

## Proved and sorry left

Proved `AdicCompletion.isNoetherianRing`
(node `lem-weil-pbc-adic-completion-noetherian`): one of one original sorries removed.
No sorry remains in this module, and no new theorem or sorry is added.

The existing imported theorem `MvPowerSeries.exists_surjective_toAdicCompletion`
(node `lem-weil-pbc-power-series-onto-completion`, module
`Sheaf.RingTheory.PowerSeriesOntoCompletion`) still contains its original sorry.
This delivery reduces completion Noetherianity to that previously stated theorem
and the proved Mathlib ingredients; it does not claim an axiom-free closure.

The argument works for arbitrary ideals, including the zero and unit ideals,
for the zero ring, and for an empty generating family (`n = 0`). It adds no
properness, nontriviality or positive-generator-count assumption.

Local compilation passed without warnings using the required `lcompile.py`.
The delivery dry run checks the server compilation and preflight as well.

## No longer needed

None of the original imports, nodes or modules is pruned: each belongs to the
original argument and is used. A trial direct proof import of
`Mathlib.RingTheory.Noetherian.Basic` was removed before delivery because
`Mathlib.RingTheory.MvPowerSeries.Equiv` already provides the needed theorem
and finite-generation lemmas. Both statement imports remain public; the added
power-series import is private to the module's proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The existing node already corrects
an earlier search claim that multivariate power-series Noetherianity was absent
from Mathlib. The pinned Mathlib contains the required instance in
`Mathlib.RingTheory.MvPowerSeries.Equiv`.

Fresh searches through `msearch.py` used LeanFinder for completion Noetherianity,
Loogle for `IsNoetherianRing, Function.Surjective`, and grep for completion,
surjective-image Noetherianity and finite generating families. LeanFinder found
flatness and related completion results, without the requested conclusion;
Loogle found `isNoetherianRing_of_surjective`; grep confirmed that theorem and
`Submodule.fg_iff_exists_fin_generating_family`. Direct searches of the source
library and Sheaf found no shorter proved completion-Noetherianity result.

## Second reading by T1

1. **Diff and visibility.** Compared the delivered module with the repository
version: the theorem signature, docstring, and existing declarations are unchanged;
the only code change is the proof and one proof-only import.
2. **Compilation and axioms.** Compiled the module with `lcompile.py` successfully.
The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`; no definition is hollow. Its only unresolved dependency is the
already split theorem `MvPowerSeries.exists_surjective_toAdicCompletion`.
3. **Statements and searches.** No statement was split off. The existing target
statement is unchanged, and searches found no shorter duplicate theorem in the
library or Mathlib.
4. **Route and pruning.** The proof follows the node's four stated steps: finite
generators, surjection from multivariate power series, Noetherianity of the source,
and descent across a surjection. All six listed proof dependencies remain used;
the added `MvPowerSeries.Equiv` import is proof-only. The unit's realized route is
unaffected.
5. **DAG agreement.** The node's proof, dependencies, and origin agree with the
Lean proof, and no new node or change record is needed.

Changed after this reading: appended this review only; no Lean or DAG repair was
necessary.
