## What changed

Proved `AlgebraicGeometry.ProEtale.internal_first_residue_ring_iso` in
`Sheaf.SixFunctors.ProEtale.InternalFirstResidueRingIso`, with its signature unchanged.
Private helpers construct the constant-function ring-presheaf map, prove local
surjectivity by its finite fibres and local injectivity using the empty cover, and
obtain an isomorphism after ring sheafification. The forgetful sheaf functor and
`Mon.mkIso'` give the required internal ring isomorphism.

Added a proof-only `import all Sheaf.Paper.DerivedNakayamaResolution` to reuse its
proved private `quotientDiscrete` theorem in the exact absolute-value topology of
the item. Added a proof-only Mathlib locally-bijective import. Original public
imports and all public statements and definitions are retained. Updated the item
node's proof, proof dependencies and proof origin to describe this construction.

Validation: the final module compiled cleanly through `lcompile.py` in 6.9 seconds,
with no errors or warnings. Both added imports passed the import-direction check.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.internal_first_residue_ring_iso`
(node `lem-sfb-internal-first-residue-ring-iso`).

One hole closed; zero holes added; zero holes remain in the delivered module.
All private helpers are complete. No split-off statements or definitions were added.

## No longer needed

The proof does not need `FiniteDiscreteOrdinary.encoding_exists`
(node `lem-sf-finite-discrete-normalized-encoding`): constructing the point ring
isomorphism directly avoids its additional scheme module-category equivalences.
It also does not need `IntegralConstantModel.pointComparison` or
`IntegralConstantModel.pointEquality`
(node `def-sfb-integral-constant-model-realization`): quotient discreteness is
already proved in the precise topology used by `DerivedNakayama.quotientRing`.
These two nodes were removed from the proof-dependency list. Their existing
statement-dependency entries and the original public imports are retained.

No library module is withdrawn, and no global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned general normalized encoding was more
than the item needed; its finite-fibre sheafification argument suffices on the
point. The existing `DerivedNakayama.quotientDiscrete` already handles the spectral
versus absolute-value topology comparison, so that calculation need not be repeated.
The finite-fibre argument works for the zero ring and empty test object; the latter
uses the empty covering family. No unit route or target statement changes.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
