## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.etale_pullback_relation_presheaf` in
`Sheaf.AlgebraicGeometry.EtalePullbackRelationPresheaf`, preserving its entire statement
and all public imports. Added private proof imports of Mathlib's Type coequalizer model
and preservation API, and three proved private helpers for sectionwise coequalizers
and étaleness of the two underlying pullback projections in `Over S`.

The proof constructs the canonical three projections, proves their universal property
and middle-coordinate uniqueness, and checks the pulled-back relation's monicity and
equivalence axioms. Both projections are étale by base change and composition. Evaluation
preserves coequalizers; the Type coequalizer quotient and equivalence closure identify
class equality with an actual relation witness. Coequalizer descent constructs the
natural map, and representatives prove its sectionwise injectivity.

Updated the existing node's proof to record the direct second-projection factorization
and the Mathlib implementation of the quotient argument. All three declared proof
dependencies remain used as Mathlib leaves. The unit route is unchanged.

Validation: server single-file compilation passed without warnings after removing the
unused trial import. `#print axioms` reports exactly `propext`, `Classical.choice`, and
`Quot.sound`. The delivery preflight checks the unchanged public statement again.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.AlgebraicSpace.etale_pullback_relation_presheaf`
(node `lem-trf-etale-pullback-relation-presheaf`).

Proved 1 of 1 original sorries; added 0 holes; split off 0 statements.
No sorry remains in the delivered module or its three private helpers.

## No longer needed

No existing import, node, module, or declared proof dependency is pruned.
The trial proof import `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks`
was removed after compilation showed the existing imports already provide the API.
The planned reassociation through `U′ ×_U R` with respect to t is unnecessary:
the existing iterated pullback's second projection is already the base change of the
étale composite `pullback.snd g s ≫ t`.

## Where the brief, the DAG or earlier work was wrong

No statement defect or tool failure was found. The DAG's second-projection argument
was correct but longer than necessary; its proof step now follows the direct base-change
argument actually used. Empty section sets need no inhabitance assumption: the
coequalizer projection is surjective even when its source and target are empty.
No public definitions or signatures changed, and no consumer adaptation was necessary.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
