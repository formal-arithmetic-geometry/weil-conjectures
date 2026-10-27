## What changed

Proved `CategoryTheory.relative_hom_witness_transport` in
`Sheaf.CategoryTheory.RelativeHomWitnessTransport`, preserving its full statement,
universes, hypotheses, visibility and public imports. The proof constructs the
common equivalence as precomposition with `q.hom`, followed by `a`, followed by
postcomposition with `θ.hom`. Naturality and the image normalization identify every
witness formula with that equivalence. Mathlib's `FullyFaithful.isoEquiv` supplies
the unique lifted isomorphism. The remaining clauses are explicit naturality,
inverse, essential-image uniqueness and identity-transpose calculations.

Updated the existing node's proof, proof dependencies and proof origin to record
these calculations. No new declarations, modules, definitions or interfaces.
The module and source docstrings retain their original source and seven-step plan.
Single-file compilation succeeded; delivery performs the final warning and axiom checks.

Searches: leanfinder found `FullyFaithful.preimageIso` and `isoEquiv`; loogle
confirmed `FullyFaithful.isoEquiv`; Mathlib grep found `Iso.homFromEquiv` and
`FullyFaithful.nonempty_iff_map_bijective`. Searches of both project library roots
found no duplicate of this theorem. Read both dependency signatures and the unit
record; the unit's statement and realized steps are preserved.

## Proved and sorry left

Closed one original hole:
`CategoryTheory.relative_hom_witness_transport`
(node `lem-sf-relative-hom-witness-transport`).

Holes added: zero. Sorries left in the delivered module: zero. Split off: zero.

## No longer needed

No imports removed and no modules withdrawn. Both existing public Mathlib imports
are retained, preserving the established exported interface; no proof-only imports
were added.

Removed `lem-weil-pbc-adjunction-of-natural-bijection` from proof dependencies:
the two identity-transpose clauses follow by substitution and equivalence inverse
laws; `Adjunction.mkOfHomEquiv` is not needed to construct a relative equivalence.
It remains a statement dependency explaining the naturality convention. This is
a Mathlib leaf, so no project module is pruned. `def-nagata-category` is retained.
The full unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan is valid; its bijectivity and unique
isomorphism steps are implemented using existing Mathlib equivalences rather than
reconstructing their inverse laws. The final two clauses need no construction of
a global adjunction. The naturality assumptions on `b` are redundant in the
presence of its normalization against `a` and `θ`; they remain in the statement.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
