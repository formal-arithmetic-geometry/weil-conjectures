## What changed

Filled the proof of `AlgebraicGeometry.genericComponent_etale_local_support` in
`Sheaf.AlgebraicGeometry.GenericComponentEtaleLocalSupport`. Its signature, the real
construction `genericComponentEtaleLocalIdeal`, and all public imports are unchanged.

The proof constructs and proves limiting the one-member wide pullback cone, then applies
the existing `finiteIntersection_etale_stalk_model` to the actual stalk kernel. It uses
the proved `Scheme.Hom.ker_stalkMap` to supply the affine ideal equality required by that
model. The resulting quotient spectrum isomorphism is over the ambient local spectrum.

A proved private helper assembles étale stalk dimension invariance from affine charts and
`RingHom.Etale.ringKrullDim_localization_eq`. Its proof follows the already proved private
`etale_stalk_dimension` in `EtaleCoordinateIntersectionGeometry`; it does not import that
module or the larger `etale_stalk_invariants` conjunction. Applying it to the first
projection of `Z ×_X W` makes the quotient dimension zero. The dimension-zero local
spectrum API gives uniqueness of its point, the surjective quotient map gives its closed
point image, and maximality of irreducible components proves the singleton component
formula. The final clause uses the canonical `stalkClosedPointIso`.

Added private proof imports of the finite-intersection model, the proved source-library
closed-immersion complements, `Mathlib.RingTheory.KrullDimension.Zero`, and the local ring
homomorphism API. Updated the item's DAG proof, proof dependencies and proof origin to
match this argument. No existing module other than the assigned item changed; no shared
interface changed. Both new project imports pass `tools/import_direction.py may`.

Validation: the final single-file `lcompile.py` run succeeded with exit code 0 in 3.9 s,
with no warnings or errors. Text checks confirm zero `sorry`, all lines at most 100
characters, unchanged theorem signature, unchanged ideal definition and public imports,
and changes to only the permitted proof fields of the item node.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.genericComponent_etale_local_support`
(node `lem-trf-generic-component-etale-local-support`). The private helper
`etale_stalk_dimension` is also fully proved.

Item holes before: 1. Item holes after: 0. Holes added: 0. Split-off statements: 0.
No `sorry` remains in any delivered Lean file. This proves the item from existing
stated dependencies; `finiteIntersection_etale_stalk_model` remains an existing
unfinished dependency, and this delivery does not claim its proof or transitive
axiom-freedom.

## No longer needed

Removed the original private imports `Mathlib.RingTheory.Localization.Ideal` and
`Mathlib.RingTheory.LocalRing.Quotient`. The proof needs only the explicit local
homomorphism theorem `IsLocalHom.of_surjective` from
`Mathlib.RingTheory.LocalRing.RingHom.Basic` for the quotient map.

Removed the direct proof dependencies `lem-weil-pbc-etale-ring-base-change` and
`lem-weil-pbc-localization-at-prime-of-quotient` from this node. The finite-intersection
model already supplies the quotient-to-pullback-stalk ring isomorphism, so applying
scheme étale base change and the same affine-chart dimension argument to its first
projection replaces the separate tensor-product and quotient-localization calculation.
These two nodes remain dependencies of the existing finite-intersection model; no global
withdrawal or removal of their modules is claimed. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement, definition defect, or tool defect found. The original DAG's longer
quotient-chart argument was unnecessary because the declared finite-intersection model
already includes the stalk isomorphism at the point of `Z ×_X W`. The updated proof uses
that existing conclusion. The unit route is preserved, and the item is not itself a
unit statement or realized unit step. No new nodes, signature changes, or forced
consumer adaptations were needed.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
