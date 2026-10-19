## What changed

Completed the three existence-and-uniqueness proofs in
`Sheaf.Paper.ExceptionalFiniteSupportRealization`, preserving all existing signatures,
visibility, definitions, docstrings and public imports. Added two proof-only imports:
`Sheaf.CategoryTheory.MateIsoAlongEquivalences` and
`WeilConjectures.CategoryTheory.InverseMateEquivalence`.

The ordinary open comparison is the inverse mate of the existing inverse-image
comparison. Four proved private helpers derive the full Hom-transpose equation and
uniqueness from the mate unit equation. The exact derived comparison descends the
ordinary complex comparison through `DerivedCategory.Q` by localization full
faithfulness. Its normalization is proved as an identity of composite natural
isomorphisms; uniqueness cancels the invertible normalization factors and uses
`Localization.natTrans_ext`. The exceptional right-adjoint comparison is the forward
mate of the inverse compact-support comparison, and its uniqueness follows by
evaluating the transpose equation at the counit.

Updated `def-pur-adic-support-realization` with these three proof steps and their
actual declared dependencies. The blueprint unit statement and its route are kept.
No statement or definition repair, consumer adaptation, or change record is needed.

Validation: the full module compiles cleanly through `lcompile.py` (50.5 seconds).
Both proof-only imports pass `tools/import_direction.py may`. All lines have at most
100 characters. The final delivery check also runs the project's axiom probe.

## Proved and sorry left

Closed all 3 original holes:

- `WeilConjectures.integralExceptionalEtaleOpen_existsUnique`.
- `WeilConjectures.integralExceptionalEtaleDerivedOpen_existsUnique`.
- `WeilConjectures.integralExceptionalEtaleRightAdjoint_existsUnique`.

All three belong to node `def-pur-adic-support-realization`. Zero holes remain in the
delivered module, zero holes are added, and zero statements are split off. The proof
uses the existing finite-realization interface, whose unfinished prerequisites are
outside this delivery. This is a proof of all three assigned statements from the
library's declared dependencies.

## No longer needed

None. No imports, modules, or DAG nodes are pruned. The original sole public import
is needed by the statements and constructions; each added proof-only import is used
by one of the two mate arguments. The original node had no proof steps or proof
dependencies to prune. No new theory of compact support or representatives is needed:
the existing adjunctions, mate invertibility, and Mathlib localization API suffice.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof plan even though the declaration docstrings already gave
usable arguments. Its proof field now records the actual implementation. There is no
mathematical statement defect and no departure from the unit route.

The interrupted sandbox contained a partial draft. It was resumed with the original
sandbox and budget. Its remaining coercion and cancellation errors were repaired using a generic localization
comparison helper and explicit functor expressions;
no delivery was repeated without checking the preceding tool result.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
