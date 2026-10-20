## What changed

Proved `AlgebraicGeometry.Scheme.purTwistZlAction_existsUnique` in
`Sheaf.Paper.PurTwistSheafLocallyFree`, preserving every existing statement,
definition, visibility and import.

Three fully proved private helpers supply the argument. `purTwistTorsionMap_smul`
pulls the normalized torsion action back along a morphism of constant coefficient
rings and applies the existing automatic-linearity theorem for additive sheaf
morphisms. `purTwistTransition_smul` specializes this to the actual root power
transition and finite coefficient reduction, through the existing coefficient
comparison isomorphisms. `purTwistCoordinateModule` transfers module laws through
jointly injective additive coordinates.

For each object of the site, the scalar multiples of the finite root coordinates
form a cone of sets. The actual root limit represents this cone because sheaf
limits, evaluation, and the abelian-group forgetful functor preserve limits.
Joint injectivity proves the module identities and uniqueness; naturality of the
root and coefficient projections proves compatibility with restriction. This
implements the coordinate-action portion of step 4 of the existing node, without
requiring local trivializations or an invertibility assumption on the base.
The proof also works on the empty scheme.

The complete module compiled without warnings through `lcompile.py` in 24.7 seconds.
An explicit `#print axioms` check of the proved declaration reported precisely
`propext`, `Classical.choice`, and `Quot.sound`. The temporary axiom probe is omitted
from the delivered module. No new proof dependency or public API was introduced.

## Proved and sorry left

Closed 1 of the original 3 holes:

- `AlgebraicGeometry.Scheme.purTwistZlAction_existsUnique`.

Added 0 holes; split off 0 statements. The following 2 original named theorem
holes remain unchanged, both attached to node
`lem-pur-twist-sheaf-locally-free`:

- `AlgebraicGeometry.Scheme.purTwistIntegralAction_existsUnique`: the completed
  action on the sheafified integral tensor, its normalizations and uniqueness.
- `AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free`: finite root
  trivializations, compatible local bases of the root tower, the finite integral
  basis and coefficient pushout comparison, finite reductions, constructibility,
  and derived completeness.

This is a partial proof delivery under the brief's rule for modules with several
holes. All three new private helpers are completely proved. No definition
contains `sorry`, and the closed theorem does not depend on `sorryAx`.

## No longer needed

None. No imports, nodes or modules are removed. The existing dependency imports
are retained for the unchanged remaining main argument. The proved coordinate
action follows the existing node's step 4, so no route or dependency update is
needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The existing automatic-linearity
API for normalized constant torsion sheaf modules handles compatibility with
coefficient reduction after pulling back the target action. Consequently this
part of the construction needs no separate local-section or root-trivialization
lemma. The rest of the recorded route remains in place.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
