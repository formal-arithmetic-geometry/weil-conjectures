## What changed

Proved `AlgebraicGeometry.coproduct_fpqc_effectivity` in
`Sheaf.AlgebraicGeometry.CoproductFpqcEffectivity`, without changing its signature,
visibility, docstring or imports. The node copy updates step 3 to cite the existing
Mathlib leaf `lem-weil-pbc-qcqs-morphism-permanence` for the compactness API
actually used. Four private helpers implement the existing
DAG steps, with the last combining the geometric assertions: an injective family of component inclusions gives an open immersion;
restriction of the fold map along an open immersion gives the labelled coproduct
pullback; a compact open immersion into a coproduct factors through finitely many
components.

The main proof constructs the finite set and both required comparison equations.
Finite coproducts of affine schemes are affine. The compact source over the affine
base has a quasi-compact structure morphism, so base change to each smaller affine
open stays compact. Base change of the chosen inclusion gives the required open
immersion with the same labels and both comparison equations. Finally the proved
open condition is supplied to the existing
`CategoryTheory.Over.DescentDatum.isEffective_of_indQuasiAffine_fpqc`.

Validation: the required `lcompile.py` single-file compile passed in 5.1 seconds
with no errors or warnings after correcting three elaboration/API details. An
earlier service request returned no answer and was retried as instructed. The public theorem
signature is byte-identical to the shared repository source, and the module has no
`sorry` tokens or lines longer than 100 characters. Empty labels and empty schemes
require no case exclusions:
the finite-subcover, finite-affine-coproduct and pullback constructions all apply.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.coproduct_fpqc_effectivity`
(node `lem-sfb-coproduct-fpqc-effectivity`).

No sorry remains in the delivered module. No holes added or split off.
The imported general effectivity theorem remains an existing dependency; it is not
claimed proved by this delivery.

## No longer needed

None. No imports removed, no nodes or modules withdrawn. All declared dependencies
remain represented by the original route and its Mathlib tools. In particular the
unit's ind-quasi-affine descent route is retained.

## Where the brief, the DAG or earlier work was wrong

No statement correction required. The compact-intersection calculation in DAG step 3 is
implemented through Mathlib's equivalent API: a map from a compact scheme to a
quasi-separated scheme is quasi-compact, and quasi-compactness is stable under
base change. The affine base supplies quasi-separatedness. The local private
helpers implement elementary steps already stated by the node, so no new node or
interface change is needed. The existing Mathlib leaf
`lem-weil-pbc-qcqs-morphism-permanence` is added to step 3 and the proof dependencies.
No new general result is assumed.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
