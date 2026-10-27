## What changed

Proved the unchanged `coordinateAdjunction_composition` statement using five
proved private helpers in the item module. They establish inverse-compositor
naturality, abstract pasted transposition, compatibility of the exceptional Hom
bijection with equality transport, and the general pasted-counit identity before
and after transport. The coordinate theorem specializes the transported identity
to `zero B r`, `lastSection B r`, and `zero_successor` by direct application.

Added the proof-only import `Sheaf.Paper.AffineSpacePurityComparison` for the
recorded `compositionInverse` and `transposeComposition`. No public signature or
definition changes. The unchanged current source of that dependency is retained
in the sandbox for joint compilation: the initially published compiled version
had the older expanded definition without `transposeComposition`.

The paired compiler run verified the proof; profiling measured 0.094 seconds
for the coordinate theorem's kernel check and 0.211 seconds for all kernel checks
in the item. Profiling and trace options were removed before delivery. The proof
follows the existing node's plan and retains its dependencies and the unit route.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinateAdjunction_composition`
(node `lem-pur-coordinate-adjunction-composition`).

One of one original holes closed; zero holes remain in the item. Zero new holes
and zero split statements. All five added private lemmas are proved. The copied
dependency is byte-identical to the current repository source and adds no holes.

## No longer needed

None. No original import, declared dependency, node, or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's missing public equality-transport lemma is resolved by a
proved private lemma: eliminate the equality of morphisms and use the existing
reflexive congruence equations. Inverse transposition and target naturality give
the first counit equation; inverse transposition gives the second. Naturality
of `originCompositionAmbient` pastes them, and source naturality transposes the
result. Its remaining transpose is the specified `compositionInverse`.

The initial compiled dependency was older than its current source. Joint
compilation exposes the source's existing categorical wrapper. Keeping the
pasting and equality-transport calculations abstract and applying their result
directly avoids expensive kernel conversions at the concrete affine tower.
No public interface repair or additional mathematical assumption was needed.

LeanFinder, Loogle and Mathlib grep found generic mate/naturality results but no
identity for these specified bounded-origin bijections. The proof uses those
existing bijections directly. It imposes no positive-rank, nonempty-base, or
nonzero-coefficient restriction, so rank zero, empty schemes and zero objects
satisfy the same equations.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
