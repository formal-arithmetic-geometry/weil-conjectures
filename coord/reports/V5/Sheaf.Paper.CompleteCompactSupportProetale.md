## What changed

Reduced `AlgebraicGeometry.Scheme.cbcOpenToPush_isIso` in the assigned module
to a strictly smaller module-level reverse-adjunction statement.
The proof identifies the completed restriction scalar map with the canonical
site-adjunction isomorphism, transports the existing clopen reverse module
adjunction through that scalar equivalence, and localizes the exact adjunction.
Uniqueness of right adjoints identifies open extension with direct image.
Full faithfulness and the two specified units prove invertibility of the actual
`cbcOpenToPush`, rather than merely an unspecified comparison of its endpoints.

Added the general module-level intermediate theorem in
`Sheaf.AlgebraicGeometry.ClopenScalarRestrictionReverseAdjunction` and the proof
import `Sheaf.CategoryTheory.ExactDerivedAdjunction`. The intermediate theorem
exposes literal scalar-identified restriction; its interface avoids importing the
ordinary/system normalization package and its conflicting instances into the item.
Local continuity, additivity and finite-limit/colimit instances are supplied
explicitly from the existing published open-extension API.
Updated the existing node's proof and proof dependencies to record this argument.

The new intermediate is proved in words from the existing reverse module
adjunction; its Lean transport is the one remaining split-off step. No arbitrary data is
chosen into a public definition: existential elimination stays within proofs.

## Proved and sorry left

Closed one of the original eight holes:
`AlgebraicGeometry.Scheme.cbcOpenToPush_isIso`.
Added one split-off hole: `AlgebraicGeometry.Scheme.clopenScalarRestrictionReverseAdjunction`
(node `lem-cbc-clopen-scalar-restriction-reverse-adjunction`).
Closing the upper hole with this lower hole is a decomposition, not a net proof.
The seven remaining existing holes all belong to
`thm-cbc-complete-proetale`:

- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_identity`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_horizontal`
- `AlgebraicGeometry.Scheme.cbcRefinementMap_isIso`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_compactifications`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_refinement`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_vertical`
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_composition_refinement`

## No longer needed

None. The clopen auxiliary argument uses adjunction uniqueness instead of a new
sectionwise decomposition proof. The unit's finite-coefficient/derived-limit route
and the dependencies for the seven untouched coherence holes remain needed.
No existing imports, modules or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The completed item cannot directly import its strict-tower realization dependency:
that module already imports this item to use its normalized open adjunctions.
The clopen auxiliary proof avoids that cycle by using the general reverse module
adjunction instead. `lem-sf-clopen-reverse-module-adjunction` is used as a ringed-site
tool from another unit; it supplies exactly the clopen reverse adjunction missing
from this unit's existing declarations. `def-weil-exact-derived-adjunction`
supplies exact localization of this adjunction. No tool approval field is edited.

The current blueprint update changes the ambient coefficient presentation. This
delivery preserves the existing completed-ring statements and proves an auxiliary
clopen comparison only; it does not claim to implement that broader migration or
alter the target statements.

## New nodes

`lem-cbc-clopen-scalar-restriction-reverse-adjunction` records the remaining generic
scalar transport of the reverse clopen module adjunction. Its hypothesis is an
abstract coefficient isomorphism and an arbitrary given left adjoint. It contains
no completed inverse limits, derived categories, or assertion about the specified
open-to-push comparison. It is therefore a strict module-level step of the proof.
No definition, signature, attribute, or public import of an existing module changes,
so no definition-change record is needed.

The attempted proof of the module transport reached the pushforward-composition
unification at the first-round deadline. Its full proof in words is in the theorem
docstring and node; the working Lean attempt is retained in scratch work only.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
