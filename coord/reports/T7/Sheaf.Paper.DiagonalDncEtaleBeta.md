## What changed

Filled `WeilConjectures.PurityFiniteSetting.diagonalDncEtaleNaturality_beta` in
`lean/Sheaf/Paper/DiagonalDncEtaleBeta.lean`, preserving its signature and docstring.
The proof uses the actual `normalGeometry` squares and one common vector model
of the source diagonal. The existing, proved `model_beta_compat` helper transports
both chart normalizations to this model. Derived site-comparison naturality and
ordered Tate coefficient composition then give the two restriction squares;
pasting and cancellation finish the required equation.

Added private proof imports and private, proved composition helpers. The proof
imports `DiagonalOrientationCompatibility` with `import all` to reuse its proved
model-transport helper and integration-isomorphism proof; it does not assume its
more specialized affine-restriction conclusion. Explicit comparison lemmas handle
the presentation wrappers; local irreducibility protects the large bundle and
exceptional-functor constructions. No shared module,
public interface, definition, instance or target statement changes.

Updated the item's DAG proof and proof dependencies to describe this implementation.
The unit route remains diagonal normal geometry followed by vector integration.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.diagonalDncEtaleNaturality_beta`
(node `lem-pur-diagonal-etale-beta-square`).

No holes added; no `sorry` remains in the delivered Lean file. The integration and
Tate dependencies are existing declarations, not new split-off obligations.

## No longer needed

No original public import is removed: both define objects used in the statement.
No module is withdrawn or claimed globally pruned.

The proof does not invoke the full `diagonalOrientationRefinement` theorem; it uses
the chart data and their normalization fields. The previous direct proof dependency
`lem-pur-diagonal-orientation-refinement` is replaced by the data node.
The outer Tate square is proved from `orderedTateCoefficientComposition`, so it
does not directly invoke `lem-pur-ordered-tate-pullback-square`. That square remains
a transitive dependency of the existing vector-integration theorem. No separate
linear-frame argument is needed: the existing Cartesian vector theorem already
allows arbitrary zero-preserving Cartesian bundle presentations.

## Where the brief, the DAG or earlier work was wrong

The original plan did not expose the already-proved generic `model_beta_compat`
helper. Reusing it avoids another split of this obligation and avoids constructing
a fully normalized chart on the common source open. One chosen model suffices,
because the same integration-normalized beta is used in both comparisons.

The original theorem is unchanged, including empty opens and relative dimension
zero. All cancellations are isomorphism identities, and none requires a nonempty
base, a frame, or positive rank.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
