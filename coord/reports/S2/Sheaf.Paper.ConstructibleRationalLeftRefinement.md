## What changed

Proved exists_rational_left_refinement with the existing signature and public import.
The proof uses the proved raw-localization natural-isomorphism descent theorem.
Private helpers give the inverse integral inclusion, surjectivity on rational objects,
identity-normalized conjugation, and the scalar functor identity after localization.
The latter uses the published rational scalar object formula and its pure-tensor map
formula at coefficient one, together with R.integralScalar_eq. The scalar square is
then the image of hs under rationalization. The equal chosen shift structures are
used exactly as supplied; Mathlib's of_whiskerLeft cancels the precomposition.

The item's DAG proof now records these actual steps. No existing shared interface,
definition, source-library declaration, or consumer is changed. There are no new modules.

## Proved and sorry left

Closed the one original hole:
WeilConjectures.ConstructibleExceptionalCoefficients.exists_rational_left_refinement
(node lem-sf-constructible-rational-left-refinement).
Zero holes added; zero holes remain in this delivery. All private helpers are proved.
This is a proof from existing dependencies, not a new decomposition.

## No longer needed

None. No existing import, module, node, or declared proof dependency is pruned.
The semilinear localization machinery remains used by the raw descent theorem and
by the fixed rational scalar extension's component formulas. No new import of its
module is needed here because those proved interfaces suffice.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original plan is valid, but its scalar step
needs an explicit bridge from the supplied restricted integral functor to the
intrinsic one: R.integralScalar_eq, full-subcategory extensionality, and the scalar-one
map formula provide it. HEq of components is combined only after supplying actual
endpoint equalities; HEq alone is not treated as equality of source and target objects.
The proof applies uniformly to identity extensions, zero objects, and empty schemes.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
