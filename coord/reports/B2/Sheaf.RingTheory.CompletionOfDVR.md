## What changed

Replaced the sole hole in `AdicCompletion.isDiscreteValuationRing` in
`lean/Sheaf/RingTheory/CompletionOfDVR.lean` by a complete proof from existing declarations.
The signature is unchanged. Mathlib infers regularity of the original local PID and proves
its dimension is one. `AdicCompletion.isRegularLocalRing_iff` transfers regularity;
`RingTheory.completion_dimension` transfers dimension. The source-library domain instance
and `IsRegularLocalRing.isDiscreteValuationRing` then give both parts of the conclusion.
This is precisely Stacks 0AP1's regularity/dimension proof using 00PD (1) iff (3).
The node proof, proof dependencies, and proof origin now describe this route.

Removed the proof-only import `Sheaf.RingTheory.AdicCompletionNoetherian`.
All public imports and statements remain unchanged. The existing module and theorem
docstrings retain the longer six-step argument, whose final steps are packaged by the
already proved regular-dimension-one DVR theorem.

## Proved and sorry left

Closed `AdicCompletion.isDiscreteValuationRing`: 1 of 1 original holes; no holes added,
none left in the delivered module. No new declarations or modules.
This is a proof from existing stated dependencies, not a claim that its transitive axioms
are closed: `AdicCompletion.isRegularLocalRing_iff`
(node `lem-weil-pbc-completion-regular-local`) and `RingTheory.completion_dimension`
(node `lem-weil-pbc-completion-dimension`) remain existing upstream holes.
Local single-file compilation passes without warnings.

## No longer needed

Removed direct import: `Sheaf.RingTheory.AdicCompletionNoetherian`.
Removed direct node dependency: `lem-weil-pbc-adic-completion-noetherian`;
its module is still a dependency of the two completion lemmas, so this does not assert
that the module leaves the entire targets' closure.

Removed direct node dependency: `lem-weil-pbc-local-completion-local-ring`.
Its Mathlib locality instance remains available in the unchanged public statement imports;
no separate computation of the completed maximal ideal is needed in this proof.

Removed node dependency: `lem-weil-pbc-dvr-unit-times-uniformizer-power`.
No separate factorization or prime-ideal classification is needed: Mathlib already proves
`IsDiscreteValuationRing.ringKrullDim_eq_one`.
No other imports, nodes, or modules of the original route are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original plan expanded arguments already proved in
Mathlib and the source library. The regular-local dimension-one DVR theorem
`lem-sc-regular-dim1-dvr` is used as an existing closed generic tool, not as a replacement
of any unit step. The item is not listed among `sk-thm-p1`'s realized statement or steps;
the completion regularity/dimension route is preserved.
The Stacks source files are not populated in this clone, so the source proof was read at
https://stacks.math.columbia.edu/tag/0AP1 and
https://stacks.math.columbia.edu/tag/00PD.
Searches were run through msearch: LeanFinder for adic completion of a DVR (only valued-field
completions returned), Loogle for `IsDiscreteValuationRing, ringKrullDim` (exact dimension
lemma returned), and grep for DVR/regular-local-ring combinations (no result).
Direct rg inspection found the Mathlib local-PID regularity instance and the source-library
regular-dimension-one DVR theorem. No new statement needed.

## Second reading by B2

1. Compared the entire delivered module with the read-only repository version using
   `diff -u`. Verdict: the existing declaration signature, public imports, definitions
   (there are none), and docstrings are byte-for-byte unchanged. Only the proof and one
   proof-only import changed; no change record is needed.
2. Independently compiled the delivered file with `lcompile.py`: exit code 0, no warnings.
   Compiled a scratch copy with `#print axioms AdicCompletion.isDiscreteValuationRing`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is expected
   from the existing completion regularity and dimension holes, not a new hole. There is
   no `sorry` or forbidden declaration/attribute in the delivered module. Verdict: a valid
   reduction of the original hole, without claiming transitive axiom closure.
3. No split-off statements, new declarations, new modules, or new nodes exist. Verdict:
   no duplicated or restated target hole. The proof uses the original DVR hypotheses;
   fields are excluded by Mathlib's DVR class, and no extra nontriviality or dimension
   hypothesis was silently added.
4. Read both completion lemmas and the existing regular-local domain instance and
   dimension-one DVR theorem. The latter has a complete proof using cotangent dimension
   and a principal nonzero maximal ideal. This four-line reduction directly transfers
   regularity and dimension, then applies that theorem; no shorter available theorem was
   found in the source/library search. Each remaining proof import supplies a declaration
   used here; the two public imports supply the signature. The report's pruned node list
   is exactly the old proof dependencies minus the new ones. Inspected
   `dag/units/sk-thm-p1.json`: the item is not a realized unit statement or step, and the
   completion regularity/dimension route is retained. Verdict: pruning stays below unit
   level and uses the closed generic DVR tool legitimately.
5. Compared the node diff and read its updated steps against the Lean proof. Only
   `proof`, `proof_deps`, and `proof_origin` changed. Their dependencies match regularity
   of a DVR, completion regularity, completion dimension, the regular-local domain
   instance, and the dimension-one DVR theorem. Statement and Lean record are unchanged.
   Verdict: DAG agrees with the proof; there are no new-node obligations.

Second reading changed only this report, adding the required independent checks and
verdicts. No Lean or node repair was necessary. The first dry run rejected only the
missing second-reading section; this section supplies it.
