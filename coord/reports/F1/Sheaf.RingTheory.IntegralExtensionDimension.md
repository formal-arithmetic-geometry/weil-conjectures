## What changed

Proved `RingHom.integralExtensionDimension` in
`lean/Sheaf/RingTheory/IntegralExtensionDimension.lean`, without changing its signature,
universes, visibility, definitions, or imports. Install the algebra structure `f.toAlgebra`
and derive `Algebra.IsIntegral R S` from `hf`. Contraction sends prime ideals to prime
ideals; `Ideal.IsIntegral.comap_lt_comap` makes this map strictly monotone.
`Order.krullDim_le_of_strictMono` then gives the dimension inequality.
For a maximal ideal, use the supplied maximality hypothesis as a local instance and apply
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'`.

This is the existing node's two-step proof, made into Lean entirely from Mathlib. The
unit `sk-thm-p1` has no realization at this node, and none of its statement or proof steps
is bypassed. No node update is needed because the proof route and dependencies are unchanged.

Searches actually run with `msearch.py`: LeanFinder for the integral-extension dimension
inequality returned dimension-at-most-one and localization results, without a general
one-lemma match; Loogle for `Order.krullDim_le_of_strictMono` returned that exact theorem;
grep for `ringKrullDim.*[Ii]ntegral|IsIntegral.*ringKrullDim` returned no match. Read the
Mathlib signatures in `Order/KrullDimension.lean`, `RingTheory/KrullDimension/Basic.lean`,
and `RingTheory/Ideal/GoingUp.lean`, including both recorded dependency declarations.
No source-library theorem was needed.

## Proved and sorry left

Closed the one original hole: `RingHom.integralExtensionDimension`
(node `lem-weil-pbc-integral-extension-dimension`). This is a complete proof, not a
decomposition: one hole closed, zero holes added, zero holes left in the delivered module.
Single-file compilation through `lcompile.py` passed without warnings.

The proof assumes neither injectivity nor nontriviality of either ring and works in the
original independent universes. For the zero target ring its empty prime spectrum is
handled by Mathlib's general dimension inequality and the maximal-ideal clause is vacuous.
Infinite dimension is covered by the same order-theoretic dimension theorem; no finiteness
or Noetherian hypothesis is introduced.

## No longer needed

None. Both original imports are used: `Mathlib.RingTheory.Ideal.GoingUp` supplies the
integrality lemmas and `Mathlib.RingTheory.KrullDimension.Basic` supplies `ringKrullDim`
and its order-theoretic interface. The original proof dependencies
`def-weil-pbc-integral-closure`, `def-weil-pbc-krull-dimension-ring`,
`lem-weil-pbc-integral-incomparability`, and
`lem-weil-pbc-integral-maximal-contracts-maximal` are all still used, with the last two
already Mathlib leaves. No project modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was required. The recorded Mathlib ingredients
suffice for the complete proof. The local literature checkout does not contain
`literature/stacks-project/algebra.tex`, so the source was read on the official Stacks
pages instead: [00OJ](https://stacks.math.columbia.edu/tag/00OJ),
[00GT](https://stacks.math.columbia.edu/tag/00GT), and
[00OI](https://stacks.math.columbia.edu/tag/00OI). Their statements and the proof of 00OJ
agree with the existing node and this implementation.

## Second reading by F1

1. **Comparison with the repository.** I diffed the delivered module against the
repository version. The theorem signature, universes, visibility, definitions, and
imports are byte-for-byte unchanged; only the original proof body was filled in. No
node or change record was altered.

2. **Proof and axioms.** The module compiles cleanly with `lcompile.py`. The theorem
contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; a
scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
The proof installs `f.toAlgebra`, obtains `Algebra.IsIntegral R S`, applies the strict
contraction map on prime spectra for the dimension bound, and applies the Mathlib
maximal-contraction theorem for the second conjunct.

3. **Statements and split-offs.** No statement was split off and no new node was
added. The existing target statement is unchanged and its edge cases (including a
zero target ring and infinite dimension) are covered by the general Mathlib results.

4. **Pruning and route.** Both public imports are used by the proof, and no import or
proof dependency can be removed. The DAG proof route and the `sk-thm-p1` unit route
remain unchanged; no unit step is bypassed.

5. **DAG and report consistency.** The existing node's proof and `proof_deps` still
describe the mathematical route (incomparability for strict contractions and maximal
contraction), while the Lean proof uses their Mathlib realizations directly. The
report records one closed hole, no added holes, and no pruned modules or nodes.

I changed only this report by adding this second-reading record; no Lean code or DAG
metadata required repair.
