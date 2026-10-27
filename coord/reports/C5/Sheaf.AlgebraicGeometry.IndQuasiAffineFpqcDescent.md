## What changed

Proved `CategoryTheory.Over.DescentDatum.isEffective_of_indQuasiAffine_fpqc`
in `Sheaf.AlgebraicGeometry.IndQuasiAffineFpqcDescent`, preserving its signature,
public imports and docstring. Added three proved private helpers in that module:
`effective_open_embedding`, `effective_spec`, and `effective_of_affine`.
No other Lean module is changed.

The proof follows Stacks `more-groupoids.tex`, Tag 0APK,
`lemma-ind-quasi-affine`, read in full. The affine-spectrum case chooses invariant
neighbourhoods inside invariant intersections. The existing
`invariant_open_affinization_equivariance` supplies an actual affine datum and
an equivariant open embedding. Affine flat descent makes that datum effective.
The first helper proves equality of the inverse-image opens on the kernel pair,
uses fpqc descent of open subschemes, pastes the pullback squares and cancels the
open inclusion to prove transport invariance. The existing invariant-open gluing
then gives global effectivity. The second coordinate helper conjugates every
transport through the affine cover/base isomorphisms and checks its three laws,
then transports the effective square back.

For a general singleton cover, used the existing component lemmas of the affine
reduction: affine-base gluing, finite affine refinement, canonical pullback datum,
and reflection of effectivity through the refinement. This avoids a separate
finite-coproduct permanence proof for the ind-quasi-affine property, which the
singleton reduction does not use. The item's node records these steps and the
actual dependency union. No new node and no definition/interface repair.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.Over.DescentDatum.isEffective_of_indQuasiAffine_fpqc`
(node `lem-a1-ind-quasi-affine-fpqc-effective-descent`).
Added 0 holes; 0 holes remain in the delivered Lean module. The private helpers
are fully proved. No split-off theorem. This is a proof from existing statements,
including the existing holed theorem
`AlgebraicGeometry.invariant_open_affinization_equivariance`; its hole is neither
copied nor moved. Compilation validation is recorded by the delivery tool.

## No longer needed

Removed these redundant direct proof imports:

- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
- `WeilConjectures.AlgebraicGeometry.FpqcDescendingTypesMorphisms`
- `WeilConjectures.AlgebraicGeometry.AffineFpqcDescent`
- `Sheaf.AlgebraicGeometry.IntersectionCanonicalAffineEmbedding`
- `Sheaf.AlgebraicGeometry.IntersectionSectionsFlatBaseChange`

The direct reduction dependency
`lem-galois-fpqc-descending-types-morphisms` is replaced by its existing
component declarations, with their hypotheses explicitly checked. Its
`lem-weil-pbc-scheme-coproduct-family` input is not used directly; the existing
affine-refinement theorem still uses coproducts.

The separate theorem `lem-a1-invariant-intersection-affine-descent` is not
needed directly: the equivariance theorem already supplies the affine datum F,
and affine flat effectivity is applied to that same datum. Its module remains
required for the public constructions in the equivariance interface. Likewise
canonical-affine-embedding and section-base-change remain dependencies of
equivariance, despite removal of their direct imports. No module is withdrawn,
and no claim is made that these transitive dependencies leave the targets'
closure. Obsolete direct tool approvals removed from the node are
`lem-galois-fpqc-descending-types-morphisms`,
`lem-galois-fpqc-affine-descent-effective`,
`lem-weil-pbc-flat-morphism-base-change`,
`lem-weil-pbc-scheme-coproduct-family`, and
`lem-weil-pbc-fibre-product-affine-spectra`.

## Where the brief, the DAG or earlier work was wrong

The Lean docstring still describes the older seven-step plan, whereas the DAG
was already re-split. The existing equivariance interface is stronger than that
plan needs: it supplies F and its transport compatibility, so the assembly need
not identify two independently chosen section-ring data. The delivery preserves
the mathematical statement and follows the same Gabber argument. The affine
reduction's finite-coproduct hypothesis is unused for a singleton cover, as its
existing proved implementation already demonstrates.

Checked the empty total space, empty neighbourhood, empty affine base/refinement,
and identity cover cases: the point-indexed cover may be empty, all open-descent
arguments allow empty opens, and coordinate conjugation uses only isomorphism
laws. No quasi-compactness or finite-presentation hypothesis is imposed on V.
The component reduction lemmas and affine flat descent are generic descent tools
from other units; they replace neither a mathematical unit statement nor a step
of the fixed blueprint route. Their use is recorded for the independent reader.
No unit statement or unit proof step is bypassed; this is the same descent tool
below the fixed unit route.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
