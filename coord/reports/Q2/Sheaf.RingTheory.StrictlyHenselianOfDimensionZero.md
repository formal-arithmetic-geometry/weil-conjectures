## What changed

Proved `isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero` with its signature
byte for byte unchanged. The first worker's proved private helper
`lift_idempotent_of_dimension_zero` is retained: dimension zero identifies the
maximal ideal with the nilradical, its extension to any algebra is nil, and
Mathlib's Stacks 00J9 theorem lifts idempotents uniquely.

The second reading replaced the open idempotent/root-lifting equivalence with
a direct proved lemma `henselianLocalRing_of_maximalIdeal_le_nilradical` in the
new module `Sheaf.RingTheory.HenselianOfNilMaximalIdeal`. It applies Mathlib's
`Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`: the polynomial value
is nilpotent, the derivative is a unit, and the resulting nilpotent correction
lies in the maximal ideal. This proves henselianity without an open dependency.
The original separably closed residue-field hypothesis then gives strict
henselianity. The main module has only proof-only added imports of
`Mathlib.RingTheory.KrullDimension.Zero` and the new helper module. In the new
module, the Newton import is proof-only. No definition or existing statement
changed, and no change record is needed.

## Proved and sorry left

Proved the item's sole formerly open theorem
`isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero`, the private idempotent
helper, and the new theorem `henselianLocalRing_of_maximalIdeal_le_nilradical`
(node `lem-weil-pbc-henselian-of-nil-maximal-ideal`). No sorry remains in either
delivered module or in their proof dependencies. Explicit #print axioms checks
show only propext, Classical.choice and Quot.sound. Both modules compile locally
without warnings through lcompile.py.

## No longer needed

Every old proof dependency still used is retained. The following old nodes are
no longer used by this item:
- `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`;
- `lem-weil-pbc-product-of-localizations-at-maximal`.

These are Mathlib leaves, not Sheaf modules. No original public import was
removed; all four support the public statement. The second reading also removed
the first worker's proof-only import `Sheaf.RingTheory.HenselianLocalRootLifting`
and its dependency `lem-weil-pbc-henselian-local-root-lifting`. Neither the finite
spectrum/product route nor the open idempotent/root-lifting equivalence is needed.
These pruning claims concern this item only.

## Where the brief, the DAG or earlier work was wrong

No existing statement error was found. The DAG had already found the short
00J9 route but retained the longer 06RS route. The first worker implemented 00J9
correctly, but missed Mathlib.Dynamics.Newton as a direct route to root lifting.
That route removes the only remaining sorry dependency. No Noetherian, Artinian,
or uniformly nilpotent maximal-ideal assumption is necessary. LeanSearch was
attempted but returned HTTP Internal Server Error; this is recorded as unavailable,
with no mathematical verdict. LeanFinder, Loogle, and direct source/library searches
provided the Newton lemma and ruled out an existing local-ring implication.

## New nodes

`lem-weil-pbc-henselian-of-nil-maximal-ideal` states that a commutative local ring
whose maximal ideal consists of nilpotents is henselian. Its new module contains
a complete proof from Mathlib's Newton correction theorem; its docstring and
node explain finite Newton iteration and why the correction has zero residue.
It is only the henselian part of the argument, with neither strict henselianity
nor an idempotent clause, and is not a restatement of the item. No change record.

## Second reading by Q2

1. Compared every delivered file with the repository and checked the original
   theorem signature byte for byte by extracting the text before := by. It is
   identical, including the independent universes u and v. The only additional
   public declaration is the new, separately recorded lemma. No definition changed.
2. Compiled both delivered modules locally in import order without errors or
   warnings. Scanned for sorry and forbidden declarations. Explicit #print axioms
   on both public theorems and the private helper shows only the three standard
   axioms, with no sorryAx. The nil ideal argument uses nilpotence of each element,
   not a uniform nilpotence exponent.
3. No statement is split off with sorry. Checked the new proved lemma against
   its Mathlib source and complete docstring proof. Fields have zero maximal ideal
   and satisfy it; local rings with nil maximal ideals of unbounded nilpotence also
   satisfy it because Newton iteration only needs an exponent for f(x). The zero
   algebra is allowed in the idempotent clause and is covered by the quotient
   lifting theorem. Local rings themselves are nontrivial by IsLocalRing. Searched
   Mathlib, upstream and lean/Sheaf with nilradical/maximalIdeal and Newton/root
   terminology; the general correction lemma exists but the local-ring producer
   does not. Reused the correction lemma rather than proving it again.
4. Retained the first worker's correct 00J9 idempotent proof. Replaced the open
   equivalence route by direct Mathlib Newton correction. All added proof imports
   are private; retained public imports support the existing signature. The two
   removed old proof_deps are fully listed above. Read dag/units/sk-thm-p1.json:
   this item is below the realized steps, and neither the unit route nor realized
   fields change.
5. Checked the item's unchanged natural-language statement and lean record,
   and updated its proof steps, proof_deps and proof_origin to the actual proof.
   The new node has matching verbatim Lean signature, source, proof, search records,
   chapter, unit, creation and blueprint fields. Its proof uses the Newton theorem
   plus elementary nilradical containment; it introduces no open obligation.

Changed: removed the sorry-dependent root-lifting equivalence import and proof;
added the proved nil-maximal-ideal helper module and its node; synchronized the
DAG and report. The existing theorem signature and correct idempotent proof stay.
