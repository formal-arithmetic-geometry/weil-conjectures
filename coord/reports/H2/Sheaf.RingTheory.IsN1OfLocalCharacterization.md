## What changed

Replaced the circular finite-spanning-set restatement from the first worker with two
strict parts of the Stacks Tag 0333 argument: local approximation above one maximal
ideal, and compactness patching of those approximations. The item's proof combines
them and proves the final identification of the finite intermediate algebra with the
integral closure using Mathlib. Existing signatures, definitions, visibility, public
imports and the original theorem docstring are unchanged.

New proof imports of the item are `Sheaf.RingTheory.LocalNormalIntermediateAlgebra`,
`Sheaf.RingTheory.PatchLocalNormalIntermediateAlgebras` and
`Mathlib.RingTheory.LocalProperties.IntegrallyClosed`. The original proof import
`Sheaf.Paper.NormalLocusOpen` moves to the patching lemma, where its argument uses it.

## Proved and sorry left

Hole closed in the item: `isN1_of_local_characterization`.
Holes added, both with their whole proof `by sorry`:
- `exists_local_normal_intermediate_algebra`
  (`lem-weil-pbc-local-normal-intermediate-algebra`);
- `exists_finite_locally_normal_intermediate_algebra`
  (`lem-weil-pbc-patch-local-normal-intermediate-algebras`).

This is a decomposition, not a completed proof of the N-1 criterion: one hole closed,
two added, net -1. The final normality criterion and the equality with the integral
closure are proved. The local approximation and patching arguments remain open.
The first worker's `exists_finite_span_integralClosure_of_local_characterization`
and its circular node were removed from the sandbox and are not delivered.
No definitions or data selected from an unproved existence theorem are added.

## No longer needed

The item no longer directly imports `Sheaf.Paper.NormalLocusOpen`; the patching lemma
still imports it, so no library module is made unreachable by this change.
The following old direct proof dependencies of the item move to the two helper
arguments and are no longer direct dependencies of the final reduction:
- `def-weil-ring-localization-away`
- `lem-weil-pbc-finite-algebra-noetherian`
- `def-weil-pbc-noetherian-ring`
- `lem-weil-pbc-integral-closure-commutes-localization`
- `lem-weil-pbc-normal-locus-open`
- `lem-weil-pbc-integral-spec-closed-map`
- `def-weil-pbc-localization-at-prime`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-finite-of-integral-generators`
- `lem-weil-pbc-integral-closure-algebraic-extension-normal`
- `lem-weil-pbc-localization-normal-domain`
- `def-weil-pbc-module-localization`
- `lem-weil-pbc-proper-ideal-contained-in-maximal`
- `lem-weil-pbc-affine-scheme-qcqs`

These are dependency-edge changes, not claims of module pruning. The helpers retain
the original argument, and the unit `sk-thm-p1` and its `realized` record are unchanged.

## Where the brief, the DAG or earlier work was wrong

The first worker moved the entire N-1 statement to a finite-span theorem, which is
logically equivalent to the definition of `Module.Finite`. It did not give a real
reduction, and its node depended on the very item it purported to prove, creating a
circular proof plan. Its node also lacked the required metadata and searches.
No such restatement or cycle remains. The original node's route is valid and is
retained in its two genuine partial arguments and the proved final step.
The source file is absent on this machine; the second reader checked the published
source at https://stacks.math.columbia.edu/tag/0333. LeanSearch returned Internal
Server Error; that unavailability is recorded, with successful LeanFinder, Loogle
and Mathlib grep searches as alternatives.

## New nodes

`lem-weil-pbc-local-normal-intermediate-algebra`, in
`Sheaf.RingTheory.LocalNormalIntermediateAlgebra`, isolates original step 4.
It assumes N-1 at just one maximal ideal, has no normal-principal-open hypothesis,
and concludes only a finite intermediate algebra normal above that maximal ideal.
It needs no Noetherian assumption. Its docstring gives the denominator-clearing
construction and the further-localization argument.

`lem-weil-pbc-patch-local-normal-intermediate-algebras`, in
`Sheaf.RingTheory.PatchLocalNormalIntermediateAlgebras`, isolates original steps
1--3 and 5--7. It assumes local finite normal approximations, not N-1 localizations,
and concludes a finite algebra normal at all primes. Its docstring gives closed
bad loci, the compact cover, the finite supremum and localization normality.
The final equality with the integral closure is proved in the item's module.
There are no change records because no existing interface changes.

## Second reading by H2

1. The delivered item preserves the original theorem signature byte for byte; the
   final proof compiles and closes `isN1_of_local_characterization` using the two
   strict intermediate statements and Mathlib's maximal-localization criterion.
2. The two new statements are genuine strict reductions: one handles a single
   maximal ideal and the other patches those local algebras. Their hypotheses and
   conclusions match their Lean declarations, and neither is a restatement of the
   target. Both remain explicitly named `sorry` theorems with source docstrings.
3. No duplicate declaration was found in the repository or the recorded searches;
   the available LeanFinder, Loogle and grep searches found only component lemmas.
4. The item and both helper files compile with `lcompile.py`; the item has no
   anonymous or definition-level `sorry`, and the only remaining holes are the two
   named helper theorems. The imports used by the final proof are proof-only where
   appropriate, and the old direct dependencies were removed from the item.
5. The DAG node for the target now records the two helper nodes as the reduction,
   while the unit `sk-thm-p1` and its realized route remain unchanged. I corrected
   the target node's dependency list and proof step to match the actual Mathlib
   criterion used by the Lean proof.

I changed only the target node metadata, added this second-reading record, and
removed the obsolete direct proof import from the target; no theorem statements or
definitions were changed.
