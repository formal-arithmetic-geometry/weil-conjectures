## What changed

Proved `AlgebraicGeometry.unramified_iff_exists_iso_coproduct_spec_finite_separable`
in `Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition`, preserving its exact
signature and all public imports. No other Lean module is changed.

For each point choose an affine neighbourhood, give its coordinate ring the algebra
structure induced by the given morphism, and apply the existing unramified affine
algebra decomposition. The existing finite-product spectrum theorem supplies a
field-spectrum open immersion whose image is that point. These disjoint open
immersions assemble by `Sigma.desc` into a surjective open immersion and hence an
isomorphism. The algebra equivalence's scalar compatibility proves that it is over
the original field. Conversely the finite separable summands are etale, and etaleness
of the whole morphism follows from `sigmaOpenCover` and source locality.

Updated the item's DAG proof steps and dependencies to match this implementation.
The arbitrary index set is the underlying point type of the scheme; the argument
covers empty schemes and imposes no global quasi-compactness or finiteness.

Searches through leanfinder and loogle found the algebra classification and generic
morphism-property APIs but no scheme-level theorem with this conclusion. Local
search found the already proved affine decomposition and finite-product spectrum
lemmas; these are both used. The source read was Stacks, morphisms.tex,
`lemma-unramified-over-field` (Tag 02G7), proof of (1), together with the current
blueprint unit `sk-i-curve-zero`. No unit statement or route is bypassed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.unramified_iff_exists_iso_coproduct_spec_finite_separable`
(node `lem-trf-unramified-field-fibre-decomposition`).

Original holes: 1. Remaining holes: 0. Added holes: 0. No split-off statements.
The affine decomposition and finite-product spectrum dependencies are already proved.

## No longer needed

Removed proof imports:
- `WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`:
  the proof needs only restriction along a source open immersion, supplied directly
  by Mathlib `IsZariskiLocalAtSource.comp`; no base change is used.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: the statement already writes its
  conjunction explicitly, and the proof uses Mathlib's diagonal/formal-unramified
  equivalence directly.
- `Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`: available through the
  required etale import, so its explicit import is redundant.

The proof no longer needs `lem-weil-pbc-unramified-base-change-open`; its DAG edge
was removed. The affine unramified criterion stays as a proof dependency for the
formal-unramified/diagonal API. Both existing tool dependencies,
`lem-weil-pbc-unramified-algebra-over-field-product` and
`lem-weil-pbc-spec-finite-product-fields`, are used and retained. No module is
withdrawn, and no claim is made that the removed dependencies have no other users.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The original plan's explicit
sheaf-gluing construction and converse via affine differential modules are
implemented more directly by Mathlib's disjoint-open coproduct and source-local
etale APIs. These give exactly the same scheme isomorphism and unramifiedness,
including empty and infinite coproducts. No new nodes or change records are needed.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
