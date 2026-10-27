## What changed

Filled ten of the thirteen existing theorem proofs in
`Sheaf.Paper.AdicTraceTransposeCoefficientCalculus`, preserving every public signature,
definition, and existing docstring. Full-subcategory lifting constructs the normalized
line and unit comparisons. Projection and tensor-unit naturality give
`gamma_natural`. The counit characterizes the constructed exceptional mate as the
right comparison already supplied by `RingSystem`, whose coherence fields give the
tower, identity, shift, invertibility, and exactness conclusions. Updated the item
node to describe these proofs and retain the unfinished projection/trace argument.

## Proved and sorry left

Closed these ten original holes, in namespace
`WeilConjectures.AdicTraceTranspose`:

- `lineComparison_existsUnique`
- `unitComparison_existsUnique`
- `gamma_natural`
- `change_comp`
- `change_id`
- `exceptional_tower_identity`
- `exceptional_counit`
- `coefficient_natural`
- `invertible_exact`
- `shift_calculus`

Three original whole-theorem holes remain: `sourceComparison_existsUnique`,
`sourceShift_existsUnique`, and `coefficient_calculus`, both attached to
`lem-pur-adic-trace-transpose-coefficient-calculus`. Their existing docstrings retain
the complete proof plans. No holes added; no split-off statements. This is a partial
proof delivery, not a claim to have proved the projection/trace coefficient equation.
Some closed theorems still depend transitively on the existing holes in the data
module or on `coefficient_calculus`; these are recorded dependencies, not new axioms.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.PastedMatesCounitNormalization`,
`Mathlib.CategoryTheory.Shift.Adjunction`, and
`Mathlib.CategoryTheory.Triangulated.Adjunction`. The public data import already
provides the APIs actually used.

This proof does not use `lem-sfb-pasted-mates-counit-normalization`,
`lem-weil-pbc-adjunction-shift-compatibility-unique`,
`lem-pur-derived-change-of-rings`, or `lem-sf-triangulated-right-adjoint` as additional
proof lemmas. The mate identification and the existing `RingSystem` fields replace
these proof routes. Removed the obsolete pasted-mates top-level tool approval from
the item node. The derived-change-of-rings node remains a statement dependency.
No library module is withdrawn: these nodes and their modules may have other users.

## Where the brief, the DAG or earlier work was wrong

The proof plan did not exploit the strength of the existing `RingSystem` argument:
its `Comparison.b` is already an isomorphism, carries `bShift`, and satisfies the
counit and cocycle equations; `Operation.rightExact` already proves exactness of
its right adjoint. These facts permit shorter proofs after identifying the mate.
No false statement or definition was found. In particular, the original conditional
hypotheses and all target statements remain unchanged. Edge cases including identity
coefficient extensions, zero traces, zero inputs, and relative dimension zero are
covered by the uniform categorical arguments.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
