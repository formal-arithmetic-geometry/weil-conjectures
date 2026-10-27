## What changed

Proved `CategoryTheory.ConstantCompletion.constant_quotient_kernel` in
`Sheaf.Paper.ConstantCompletionQuotientKernel`, preserving its statement and public import.
Two proved private helpers extend arbitrary coefficient functions through the underlying
set-valued constant sheaf and identify their values on constant sections. Finite generation
then supplies a fixed finite expression for every kernel section. The expression is verified
on two successive covering sieves and descended by separatedness. The reverse inclusion is
ideal-span induction via the quotient map. The node now records this actual argument.

Read Stacks `sites-modules.tex`, `lemma-completion-flat` (Tag 093M), including its
sectionwise quotient identity. LeanFinder found no matching general theorem; Loogle did not
recognize `constantSheaf`; the logged Mathlib grep found `constantCommuteCompose` and related
sheafification APIs. The proof uses Mathlib's existing concrete sheafification machinery.

The argument allows an empty generating family (the zero ideal), the unit ideal, a trivial
coefficient ring, and objects admitting an empty covering sieve: neither separatedness step
requires a covering arrow to exist.

## Proved and sorry left

Closed 1 original hole:
`CategoryTheory.ConstantCompletion.constant_quotient_kernel`
(node `new-e4-constant-completion-quotient-kernel`).

Added 0 holes. There are no remaining `sorry`s in the delivered module and no split-off
statements. Both private helpers are fully proved. No statement or definition repair was
required.

## No longer needed

No existing imports, nodes, or modules were removed. The original node listed no proof
dependencies. The only added proof import is Mathlib's local-bijectivity API; no further
Sheaf or WeilConjectures modules are needed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan did not explain why local ideal expressions yield globally defined
coefficients. Finite generation alone does not justify arbitrary gluing of coefficient
choices. Extending fixed coefficient functions through set-valued sheafification provides
global coefficients directly, and separatedness then verifies their expression locally.
No mathematical statement or unit route changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionQuotientKernel": "61d1cc71a70706c29ff50a77353f99c42f72bdc4"}, "results": {"Sheaf.Paper.ConstantCompletionFlatAndQuotientsQuotient": {"hash": "ff853abce395463f9409bb2595e1c33f7ace629a", "status": "OK"}}, "seconds": 29, "time": "2026-10-28T05:08:54+0800", "transitive": 0, "version": 1}
```

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
