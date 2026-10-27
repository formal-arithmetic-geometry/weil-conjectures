## What changed

Proved `WeilConjectures.CompactSupportFiniteProjection.refinement_realization` without
changing its statement. The proof explicitly constructs a retained etale origin,
inverts the recorded operation normalization, removes the witness by naturality,
and obtains the source and target equations by coefficient-unit cancellation and
tensor functoriality. Added the proof-only import
`Sheaf.Paper.FiniteRefinementAmbientNormalization` and the origin theorem import.

The new module proves the tensor-free, operation-datum-free normalization. It reuses
the finite clopen site-transport and bounded-below mate compatibility declarations.
Its private calculations generalize the internal proof in
`PurityWitnessedMateNormalization`, whose public theorem imposes separated structure
maps unavailable here. The compositor calculation follows the existing private proof
in `OrdinaryDerivedCompositeTranspose`. The final inverse-word calculation is proved
for arbitrary functors and then specialized, keeping the derived constructions out
of the algebraic kernel check. No existing shared interface changes.

Validation: `lcompile.py --all` compiled both delivery modules cleanly, without
warnings. The original item signature is unchanged; the node signatures and proof
dependency unions match the Lean files. Both files contain zero `sorry`s.

## Proved and sorry left

Closed the item's one hole:
`WeilConjectures.CompactSupportFiniteProjection.refinement_realization`
(node `lem-sf-finite-refinement-projection-realization`).

Also proved
`WeilConjectures.CompactSupportFiniteProjection.refinementComparisonAtWitness_inv_eq`
(node `lem-sf-finite-refinement-ambient-normalization`).

One original hole closed; zero holes added. No holes remain in the delivered
modules. Imported statements may still
contain their independently assigned holes; no such declaration was duplicated.

## No longer needed

No original import was removed and no whole module is withdrawn. The proof plan's
direct route through `lem-cbc-strict-tower-proper-open-calculus` is replaced by the
more direct finite clopen mate transport and D-plus compatibility declarations.
`lem-sf-proper-open-comparison-site-normalization` is not invoked as a separate
lemma: expansion of the existing specified isomorphism supplies the same equation.
`lem-sf-proper-open-projection-mate` is used through the definition of its mate,
without its tensor compatibility theorem. The refinement-comparison definition,
proper/open interchange, derived direct-image composition and refinement-projection word dependencies remain needed in the new
normalization module, rather than as direct proof dependencies of the item. No
global withdrawal is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan describes a constant-tower specialization, but the existing
finite clopen site-transport and bounded-below mate compatibility already provide
the required normalization directly. There is no need for another unproved split
of this obligation. Zero inputs, empty schemes and identity refinements require
only the same unit and naturality equations; no nonemptiness hypothesis was added.

## New nodes

`lem-sf-finite-refinement-ambient-normalization` records the proved inverse
retained-witness normalization, before introducing an operation datum or tensoring.
It is strictly the middle normalization calculation, and the item supplies the
remaining origin, support, coefficient and tensor transport calculations.
The generic tools `lem-pur-refinement-mate-plus-compatibility` and
`lem-cbc-finite-clopen-mate-site-transport` supply compatibility of the existing
coefficient/site maps; the projection unit has no separate declaration of these
normalizations. The derived-compositor step uses the proved source specialization
of `lem-sfb-derived-composition-adjunction-normalization`, with derived-adjunction
comparison, rather than any smooth-purity theorem. A search of the whole current
imported blueprint for "refinement comparison" returned six broader etale-support/package statements, and "ambient refinement"
returned none; none states this fixed-scalar inverse-word normalization. The new
node retains the item's `fix-prop-projection-formula` blueprint ancestry. No
maintainer tool approval was edited. No change record is needed: no existing
shared interface was changed.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
