## What changed

Proved `AlgebraicGeometry.exists_universalIsomorphismOpen` in
`Sheaf.AlgebraicGeometry.UniversalIsomorphismOpen`, with its signature unchanged.
Added the two private proof imports
`Sheaf.AlgebraicGeometry.UniversalSurjectiveFlatOpen` and
`Sheaf.AlgebraicGeometry.UniversalClosedImmersionOpen`.

The proof follows all five steps of `lem-sfb-universal-isomorphism-open` and
Stacks Tag 05XD (`spaces-more-morphisms-lemma-where-isomorphism`). Universal
closedness supplies `p.isClosedMap`, and typeclass inference supplies local
finite type from local finite presentation. Obtain the two opens from the
existing universal-locus theorems and intersect them. A local proved equivalence
identifies factorization through any open with containment of the underlying
image, using `IsOpenImmersion.lift` and its factorization equation. The
intersection condition is then `Set.subset_inter_iff`. For the reverse
implication, install the surjectivity, flatness and closed-immersion hypotheses
and apply `Flat.isIso_of_surjective_of_mono`; the closed immersion supplies
monomorphism and quasi-compactness. The forward implication uses the standard
instances for isomorphisms. The argument applies to arbitrary test schemes,
including empty and nonreduced ones, without a pointwise-to-universal shortcut.

Searches through the source library and Sheaf, plus the launcher's LeanFinder,
Loogle and grep searches, found no shorter universal-locus theorem. Loogle and
grep confirmed the existing Mathlib isomorphism criterion. No route, node,
public import, definition or consumer interface changed.

Validation: the final module compiled through `lcompile.py` in 4.1 seconds,
with no errors or warnings. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_universalIsomorphismOpen`
(node `lem-sfb-universal-isomorphism-open`).

Zero holes remain in the delivered module; zero holes were added or split off.
The proof uses the existing stated dependencies
`AlgebraicGeometry.exists_universalSurjectiveFlatOpen` and
`AlgebraicGeometry.exists_universalClosedImmersionOpen`; their existing proofs
remain `sorry` in their own modules. They are the intended dependencies of this
stage-3 proof, not new holes introduced by this delivery.

## No longer needed

None. Every planned dependency is used, and no import, node or module is pruned.
The two new imports are proof-only. The existing FlatMono proof import is used
by the final isomorphism criterion. The DAG proof and its dependencies already
match the implemented argument and therefore need no edits.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The supplied proof plan translates
directly into Lean from its existing declarations. No new nodes, adaptations or
change records are required.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
