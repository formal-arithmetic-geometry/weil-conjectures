## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.TensorCoefficientActionOnSummand` by a compiling reduction,
keeping the existing declaration, signature, visibility and docstring unchanged.
Added the proof-only import
`Sheaf.AlgebraicGeometry.TensorIdealSectionCoefficientComparison`.

The proof first applies `tensorHomogeneousKernel_action` to the independent degrees
`a = n * (0 + 1)`, `d = n * (e + 1)`, and `t = n * ((e + 1) + 1)`.
It then applies `tensorIdealSectionMultiply_coefficient_comparison` to the raw
multiplication map on Z. Pushforward functoriality, expansion of isomorphism
composites, and associativity give the exact composite in the original conclusion.
The equation identifying the output degrees is proved by distributivity in Lean.
No positivity or distinct-degree assumption is used.

Two new modules isolate different parts of the original argument:

- `TensorHomogeneousKernelAction` constructs raw ideal multiplication and its
  transport to degree kernels explicitly, and states the quotient-action identity
  in arbitrary degrees. It has no block exponent, comparison package D, or
  cohomology assertion. Its explicit constructions choose no arbitrary data.
- `TensorIdealSectionCoefficientComparison` states the monoidal comparison of
  that raw multiplication with the coefficient tensor-power multiplication on Z.
  It involves no presentation T, action sigma or mu, or kernel transport.

Updated the parent DAG proof to this reduction and supplied nodes for both
remaining statements, with sources and complete proofs in words.

All three delivered modules compile using lcompile.py, with no warnings.
Scratch checks also compiled the zero-section cases of raw ideal multiplication
and of mulTensorPowSection, independently of either new theorem, using the existing
additive tensor structure. The zero degrees were checked against the recursive
unit and tensor-power definitions; the statements impose no positive-degree
hypotheses. Scratch files are outside the delivered lean/ tree.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.tensorGradedCoefficient_action_on_summand`
(node `lem-sc-tensor-coefficient-action-on-summand`). There are no direct sorries
left in the item's module.

Added exactly two holes, both as whole proofs of named public theorems in separate
new modules:

- `AlgebraicGeometry.Scheme.Modules.tensorHomogeneousKernel_action`
  (`lem-sc-tensor-homogeneous-kernel-action`): the local lift computation, descent,
  and identification with the explicitly constructed raw kernel map.
- `AlgebraicGeometry.Scheme.Modules.tensorIdealSectionMultiply_coefficient_comparison`
  (`lem-sc-tensor-ideal-section-coefficient-comparison`): the monoidal tensor-power
  coherence calculation on Z, independently of the quotient action.

This is a decomposition, not a complete proof or a net reduction in holes:
1 original hole closed, 2 lower holes added, net minus 1. The combining proof
contains no sorry. Neither remaining statement is the original statement with
its hypotheses repackaged: one computes the action without coefficient coordinates;
the other compares coefficient coordinates without any action.

## No longer needed

No existing import was removed, and no module is claimed pruned.
The old direct proof dependencies
`lem-sc-square-zero-tensor-graded-presentation` and
`lem-weil-pbc-closed-immersion-unit-quotient` are no longer direct dependencies
of the parent reduction. They remain proof dependencies of the new
`lem-sc-tensor-homogeneous-kernel-action`; their modules are still needed.
`lem-sc-square-zero-ideal-tensor-unit` remains a direct dependency.
The original public import of SquareZeroTensorGradedProductProjection is required
for tensorGradedSection in the unchanged statement. The original presentation,
closed-immersion quotient, and ideal/unit comparison ingredients remain needed
in the new lower nodes. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error identified. The parent node's single proof step combined
local quotient-action descent with a separate monoidal coefficient comparison.
Those calculations are now separate Lean statements. Existing tensor-section
product comparison lemmas concern products of two sections; their signatures do
not supply the needed coefficient-module morphism equality.

The saved attempt used `have` instead of the original `letI` in the theorem
statement. Restored both original `letI` lines: the signature now matches the
repository and parent node verbatim, and all three modules still compile.

The unchanged hrestrict hypothesis is not needed by this reduction: mu is already
a sheaf endomorphism and hglobal specifies its restrictions for the global quotient
section used here. It remains in the original signature.

## New nodes

`lem-sc-tensor-homogeneous-kernel-action`, module
`Sheaf.AlgebraicGeometry.TensorHomogeneousKernelAction`: arbitrary-degree action
on a single kernel, expressed through explicit ideal tensor multiplication.
Source: Stacks 09MS, graded ideal sequence, and 0B8S, quotient action.

`lem-sc-tensor-ideal-section-coefficient-comparison`, module
`Sheaf.AlgebraicGeometry.TensorIdealSectionCoefficientComparison`: equality of
explicit tensor maps on Z under the canonical coefficient-degree comparisons.
Source: Stacks 09MS, tensor powers, and 01CD, pullback of tensor products.

No existing interface or target signature changes; no change records or forced
adaptations are needed.

Current retry verification (2026-10-14): all three modules compiled with exit
code 0 (3.0 s, 2.0 s, and 5.8 s). The required deliver3.py --no-push printed
OK: the latest fetched base contains the assigned module and parent node again.
The preflight passes except for the second reading, which the second reader
writes. Nothing was pushed. The earlier stale-base blocker is resolved.

## Second reading by P3

1. **Interfaces: PASS.** Compared the delivered item against the repository by
   `diff -u`. The sole existing theorem's signature, including both `letI`
   binders, its visibility, and its docstring are byte-for-byte unchanged.
   Only a plain proof import and the theorem body differ. The other two modules
   and their declarations are new; no existing definitions or target statements
   change, and there are no forced adaptations or change records.

2. **Proof and axioms: PASS as a decomposition.** Independently compiled all three
   modules with `lcompile.py --all`, without errors or warnings. Compiled copies
   under `scratchpad/second-reading` with `#print axioms` for all five new/changed
   declarations. `tensorIdealSectionMultiply` and `tensorHomogeneousKernelMap`
   use only `propext`, `Classical.choice`, and `Quot.sound`: their data have no
   dependency on `sorryAx`. The three theorems additionally use `sorryAx`, as
   expected from the two reported open statements. The only direct sorries are
   whole proofs of those two named public theorems, each with a blueprint node,
   source, and proof docstring. No forbidden declarations or kernel bypasses occur.
   In particular the top theorem is not yet a proof using only standard axioms.

3. **Split statements: PASS.** Read both statements, explicit map constructions,
   and their docstring arguments against the definitions of the presentation,
   canonical comparisons, tensor-power regrouping, and section multiplication.
   Locally with a generator of L, the raw action sends an ideal coefficient r
   and a lifted section c to cr in degree d+a; the coefficient comparison keeps
   the ideal factor fixed and appends the block represented by f. Degree zero
   uses unitors, and e=0 keeps precisely the initial coefficient block. These
   calculations include zero ideals and empty opens. Recompiled independent
   zero-section checks for both raw multiplication and mulTensorPowSection,
   without applying either open theorem. Both lower results are genuine parts:
   the action lemma contains no D or coefficient coordinates; the comparison
   lemma contains no T, sigma, mu, or kernel action. Neither restates the parent.
   Fresh leanfinder, loogle, and Mathlib grep searches used different queries
   about quotient-module local lifts, tensor regrouping, and monoidal naturality
   (recorded in searches.jsonl). Also searched both library roots by concept and
   read TensorGradedQuotientActionHomogeneous,
   TensorBoundaryKernelMapLocalMultiplication, TensorBoundaryKernelMapNaturality,
   and TensorGradedActionKernelSecondDiagonal. The proved homogeneous-support
   lemma does not identify the explicit multiplication map. The existing local
   coefficient calculation is still sorry and concerns a degree-n input with an
   arbitrary higher-degree section, not this arbitrary input degree with a
   degree-n section. None supplies either complete lower identity directly.
   Closing them needs the local monoidal/adjunction calculation or recursive
   tensor-power coherence, rather than a short application of an existing lemma.
   Checked the sources online because this clone has only literature indices:
   [Stacks 09MS](https://stacks.math.columbia.edu/tag/09MS) supplies the graded
   ideal sequence, [Stacks 0B8S](https://stacks.math.columbia.edu/tag/0B8S) supplies
   quotient action, and [Stacks 01CD](https://stacks.math.columbia.edu/tag/01CD)
   supplies functorial tensor pullback. The more explicit categorical arguments
   are correctly marked as written by an agent.

4. **Route and pruning: PASS after reporting repair.** Read the combining proof
   from its target down through the two lower lemmas. Its degree equation,
   pushforward functoriality and isomorphism expansion recover the exact original
   composite. Every import is required by a signature or proof. The item is below
   the unit level; sk-thm-curveestimate's realized statement is
   thm-sc-proper-cohomology and its realized steps list is empty. Nothing changes
   or bypasses that route. No modules are pruned. Corrected “No longer needed” to
   identify both old dependencies moved from the parent into the raw-action node.

5. **DAG: PASS.** Checked all three Lean statements against their node records,
   and checked that proof_deps is exactly the union of uses in each proof plan.
   The parent records the actual reduction; each new node has its own source,
   proof origin, three recorded search kinds, creation record, chapter, unit,
   blueprint ancestry, and matching Lean record. Restored the parent's historical
   reviewed and reviewed_proof fields to the repository values: only the stage-3
   owned fields should change in an existing node.

**Changes by this reader:** corrected the dependency-pruning report, restored
historical parent review metadata, and added this independent reading and scratch
verification. No Lean proof or signature needed repair. Holes closed: the one
original declaration listed above. Holes added: the two lower declarations listed
above. Net holes closed minus added is -1; this delivery is a decomposition.
