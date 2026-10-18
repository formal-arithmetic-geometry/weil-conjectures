## What changed

Proved `CategoryTheory.sequence_relative_hom_telescope` in
`Sheaf.CategoryTheory.SequenceRelativeHomTelescope`, with its signature unchanged.
Added one proved private helper, `sequential_difference_injective`: coordinate zero
and successor coordinates show that identity minus a forward shift on a direct sum
of arbitrary abelian groups is injective. This requires no injectivity of transitions.

The main proof transports this fact through the shifted comparison, then uses
Mathlib's `comp_distTriang_mor_zero₃₁` and `Triangle.coyoneda_exact₃` to prove
surjectivity of postcomposition by p. The stage maps form a cocone. Transporting
the colimit summand map through the unshifted comparison gives a homomorphism g
which kills the kernel of postcomposition by p, by `Triangle.coyoneda_exact₂`.
`AddMonoidHom.liftOfSurjective` supplies the unique factorization through p.
Colimit extensionality proves a left inverse, and direct-sum induction proves
surjectivity of the stated canonical map. Updated the item's node Steps 4–5 to
record this implementation of the source's quotient argument.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.sequence_relative_hom_telescope`
(node `lem-weil-pbc-sequence-relative-hom-telescope`).
Added zero holes; no `sorry` remains in the delivered module. No new modules.
The private coordinate helper is also fully proved.

Validation: single-file remote Lean compilation, followed by the delivery tool's
compilation, axiom probe, and stage-3 preflight.

## No longer needed

No imports, dependency nodes, or modules pruned. All three declared proof
dependencies remain used: the triangulated-category structure, the Mathlib leaf
for Hom exactness, and the colimit universal property. All six original public
imports support the unchanged statement and remain unchanged.

No explicit quotient construction is needed: factorization of g through the
surjective p_* implements the same argument. The coproduct universal-property
hypothesis hB remains in the signature; the two comparison hypotheses already
supply everything the proof uses about its supplied coprojections.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. Read the source arguments in
`literature/stacks-project/derived.tex`, lemma-compute-colimit (093W),
lemma-cohomology-of-hocolim (0CRK), and lemma-commutes-with-countable-sums (094A).
The DAG's exactness dependency is a Mathlib leaf, so no Sheaf proof import is
necessary. The inverse-factorization route avoids constructing a quotient while
retaining the stated unit route and every hypothesis. The only initial tool
issue was a transient remote compiler no-answer, resolved on retry.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
