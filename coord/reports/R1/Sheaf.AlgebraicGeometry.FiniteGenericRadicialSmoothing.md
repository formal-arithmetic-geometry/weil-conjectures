## What changed

Proved `AlgebraicGeometry.exists_finite_generic_radicial_smoothing` in
`Sheaf.AlgebraicGeometry.FiniteGenericRadicialSmoothing`, with its existing public
signature and public imports unchanged. Added proved private helpers for density of
the smooth locus, set-valued local constancy, and componentwise dimension comparison.
There are no new public declarations, modules, statements, or definitions.

The proof uses the existing generic geometrically reduced preparation theorem.
It lifts smooth generic-fibre points through the existing scheme-level
`Scheme.Hom.fiberι_mem_smoothLocus` API rather than reconstructing affine smooth charts.
For the optional sheaf of sets it pulls back the finite stratification, factors each
reduced interior through its original stratum using an isomorphic pullback projection,
and composes constant trivializations through the existing inverse-image restriction
and composition comparisons. The dense smooth open is intersected with these interiors.
The final dimension comparison embeds the specified subspace into the proper closed
complement in each containing component and applies the existing open-complement bound.

Updated the existing DAG node's proof, proof dependencies and proof origin to this route,
and removed obsolete top-level tool approvals. Added ordinary proof imports for the
set-valued inverse-image comparisons, stratification interiors, refinement geometry,
and equivalences preserving constant sheaves. No downstream adaptation is needed.

Validation: the final module compiles cleanly through `lcompile.py` (about 10 seconds).
All private helpers are fully proved, every line has at most 100 characters, and the
module contains zero occurrences of `sorry`. The preparation theorem remains an
existing project dependency; this delivery does not claim to close its separate hole.

## Proved and sorry left

Closed 1 of the item's original 1 holes:
`AlgebraicGeometry.exists_finite_generic_radicial_smoothing`
(node `lem-fin-generic-radicial-smoothing`).

Holes added: 0. Split off: 0. Sorries left in delivered modules: 0.
The theorem is proved from existing declarations, including the separately stated
`AlgebraicGeometry.exists_generic_geometricallyReduced_preparation` dependency.

## No longer needed

Removed these six direct proof imports:

- `Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime`
- `Sheaf.RingTheory.SingularIdeal`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`
- `Mathlib.RingTheory.FiniteType`
- `WeilConjectures.RingTheory.SingularIdeal`

The scheme-level smooth-fibre API replaces the direct proof dependencies
`lem-weil-pbc-flat-smooth-fibre-smooth-at-prime` and `def-weil-pbc-singular-ideal`.
The finite-stratification density API does not need a separate invocation of
`lem-weil-pbc-noetherian-finite-components`.
The reduced-source factorization argument replaces the direct dependencies
`prop-constructible-pullback`, `lemma-constructible-pullback-locally-constant`,
and `lemma-constructible-universal-homeomorphism-invariance`.
The four corresponding obsolete entries were removed from the top-level `tool_uses`:
`lem-weil-pbc-flat-smooth-fibre-smooth-at-prime`, `prop-constructible-pullback`,
`lemma-constructible-pullback-locally-constant`, and
`lemma-constructible-universal-homeomorphism-invariance`.

These are removals from this item's explicit route and direct imports. Some source
modules remain imported transitively by other retained source APIs; no claim is made
that they are globally unreachable from all targets. Definitions of constructible
sheaves and finite-type algebras remain available through retained imports. No unit
statement or realized unit step is bypassed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The proposed sheaf route cited declarations with abelian coefficient hypotheses,
whereas this item concerns sheaves valued in `Type (u + 1)`. The existing signatures
cannot be applied directly. Proved private set-valued helpers fill that interface gap
using the project's existing set-valued inverse-image comparisons and Mathlib's
coefficient-independent constant-sheaf machinery. On a reduced interior, the needed
surjective immersion is already an isomorphism, so universal-homeomorphism invariance
for sheaves is unnecessary here.

The dimension assertion needs no extra generic-fibre or component argument for Z:
any inducing subspace outside the chosen dense open, inside a containing irreducible
component, has the required bound. The stated hypotheses and conclusion remain exactly
unchanged. Empty schemes, empty interiors, and empty complements are covered by the
proofs: covers may be empty, density is valid on the empty space, and the dimension of
an empty subspace is bottom. No statement repair, change record, or new node is needed.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
