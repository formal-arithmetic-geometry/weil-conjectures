## What changed

Replaced the proof hole of `AlgebraicGeometry.Scheme.completedScalarMateCoefficientTransport`
by an explicit adjunction calculation, without changing its statement or any public import.
The completed coefficient comparison is proved quotient by quotient. The literal-ring
beta transpose is proved from the two geometric mate equations and the scalar unit equation.
The final isomorphisms are composites of the restriction, scalar-extension, and direct-image
comparisons; naturality transports the result to the prescribed `inverseObject`.

Added `Sheaf.Paper.ScalarCoefficientEquivalence`: identity restriction comparisons,
a proof that exact derived restriction by a ring-sheaf isomorphism is an equivalence,
and the unit-normalized transport of a scalar adjunction along equivalences. The latter
uses the iterated-mates/conjugation identity and proves invertibility, rather than
assuming invertibility of a scalar mate.

Added `Sheaf.Paper.NormalizedCoefficientDirectImageSquare`: the source and target
direct-image comparisons are actual constructions from the existing canonical
coefficient-change comparisons. Only their normalization square is a separate obligation.
It has no scalar-extension functor, scalar mate, beta arrow, completed ring, adic datum,
tensor model, or perfectness assumption. This isolates the direct-image part of step 3
of the original plan, rather than renaming the assigned theorem.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-derived-base-change` (06YY), `lemma-derived-pullback-composition` (0D6D),
`lemma-adjoint` (07A6), and `lemma-derived-pushforward-composition` (0D6E).
The unit's realized nodes and route are unchanged.

Validation: all three Lean modules compile through `lcompile.py`; the final item
compile is clean and takes 24.2 seconds. The new modules compiled in 5.9 and
8.9 seconds. The original theorem signature is byte-for-byte unchanged, the new
imports pass the import-direction check, and every delivered Lean line is at most
100 characters.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.completedScalarMateCoefficientTransport`
(node `lem-pbc-completed-scalar-mate-coefficient-transport`).

The new theorems `AlgebraicGeometry.Scheme.derivedRestrictIso_isEquivalence` and
`CategoryTheory.scalarAdjunctionCoefficientEquivalence` have complete proofs.
Every new definition has an explicit body without a hole.

Added one hole, the entire proof of
`AlgebraicGeometry.Scheme.normalizedCoefficientDirectImageSquare`
(node `lem-pbc-normalized-coefficient-direct-image-square`).
This is a decomposition: one original hole closed and one strictly narrower hole added,
not a net reduction in holes. No other sorry is left in the delivered files.

## No longer needed

No modules are withdrawn and no public imports are removed.

The original direct proof dependencies
`lem-sfb-kflat-scalar-comparison-normalization` and
`lem-weil-pbc-profinite-coefficient-inverse-image` are no longer used directly:
the existing normalized scalar adjunction API and coefficient-comparison projection equations
suffice. They remain available through existing imports and are still used by those APIs;
this delivery does not claim to prune them from the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly identifies the mathematics, but its listed coefficient-change
lemmas provide individual normalized comparisons, not the composition coherence of the given
normalized direct-image square under a change of coefficient presentations. That specific
square is now stated separately. The scalar adjunction and literal beta calculations are
carried out in Lean instead of being included in this remaining obligation.

No statement was weakened or disputed. The new statements impose no finiteness,
nonzero-ring, boundedness, or nonempty-site condition. Their constructions and categorical
identities include the zero ring, zero object, and empty site.

## New nodes

`lem-pbc-scalar-coefficient-equivalence` is realized by
`Sheaf.Paper.ScalarCoefficientEquivalence`. Its scalar-adjunction theorem and derived
restriction equivalence are proved. The identity and coefficient-square comparisons have
explicit bodies.

`lem-pbc-normalized-coefficient-direct-image-square` is realized by
`Sheaf.Paper.NormalizedCoefficientDirectImageSquare`. Its two comparison isomorphisms are
constructed explicitly. Its sole hole is the compatibility equation for restrictions and
right derived direct images. It is independent of scalar extension and scalar mates.
No change record is required: no other existing module, definition, or statement changes.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
