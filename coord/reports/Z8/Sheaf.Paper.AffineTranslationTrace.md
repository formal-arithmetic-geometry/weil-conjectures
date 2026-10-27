## What changed

Filled `AlgebraicGeometry.Etale.purAffineTranslationTrace` without changing any public
signature or definition. Four proved private helpers show that the ordinary action is
the identity, its specified pro-etale conjugate is the identity, and it therefore
preserves the actual integration map. The proof uses the existing coordinate-tower
`ambientAffineTranslationTrace` and the invertibility and base-change clauses of
`exists_affineSpaceTopTrace`, with precisely their selected transport and datum.
A generic private conjugation lemma keeps the category calculation independent of expensive
derived-category definitions. Finite type over the field supplies Noetherianity. Updated the item's DAG proof,
proof dependencies and proof origin to this shorter route. No new modules or public statements. The server compile accepted the full proof;
explicit comparison arguments avoid expanding large derived-category constructions.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.Etale.purAffineTranslationTrace`.
Holes added: zero. Holes remaining in the delivered module: zero. All four private
helpers have complete proofs. The imported `ambientAffineTranslationTrace` remains
an existing proof dependency with its own hole; this delivery uses its stated theorem
as required by stage 3 and does not claim to close its dependency holes.

## No longer needed

Removed four private proof imports: `Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange`,
`Sheaf.Paper.ConstantSheafSectionsLocallyConstant`,
`Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`, and
`Mathlib.Topology.LocallyConstant.Basic`.

The item no longer directly needs the proof nodes
`lem-pur-universal-translation-multiplier`,
`lem-pur-affine-constant-section-zero-detection`,
`lem-amb-compact-action-base-change`, `lem-pur-vector-integration-site-comparison`, or
`def-amb-vector-integration` as proof inputs: the already stated coordinate-tower
translation theorem supplies the ordinary equation. Cancellation of its invertible
trace proves the action itself is identity. Functoriality and the inverse equations
for the existing chart bridge and vectorSite then prove invariance of every map
out of the integration source, including the specified vectorIntegration. Thus no
chart normalization or site-integration comparison theorem is needed in this proof.
The vector-integration definitions and site-comparison module remain public statement
imports; they are not withdrawn. No module is withdrawn and no global unreachability
is claimed. The upstream coordinate-tower theorem may still need the multiplier,
zero-detection and action lemmas in its own proof.

Removed obsolete top-level tool approvals from this node: `lem-amb-compact-action-base-change`,
`lem-weil-pbc-derived-single-fully-faithful`,
`lem-weil-pbc-constant-sheaf-sections-locally-constant`, and
`lem-weil-pbc-connected-locally-constant-map`. The affine top trace and finite-type
Noetherian tool entries remain.

## Where the brief, the DAG or earlier work was wrong

The planned pro-etale normalization calculation is unnecessary once ordinary trace
invariance and trace invertibility have made the actual ordinary action identity.
This is a simplification below the unit route; the translation-invariance statement
and the specified ordinary/pro-etale constructions, universal and base-change clauses
remain unchanged. Rank zero, an empty base, the zero coefficient ring, and arbitrary
annihilating prime powers require no cancellation of scalars or nonemptiness: the
argument only cancels the trace isomorphism and the supplied comparison isomorphisms.
No flatness hypothesis is introduced.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
