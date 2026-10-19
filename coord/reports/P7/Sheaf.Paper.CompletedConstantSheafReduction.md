## What changed

Proved `AlgebraicGeometry.Scheme.CompletedConstantReduction.reduction_exists`
without changing its statement or the coefficient definitions. Constructed the map
on constant quotient sections, extended it through constant module sheafification,
and transposed it through the sectionwise scalar-extension and sheafification
universal properties. The tensor formula determines the transpose on constant
sections, which proves uniqueness. Private proved helpers implement those universal
properties and their pure-tensor formula, retaining the actual unequal site universes.

Also proved `finiteReduction_exists` by the same two universal properties. The
constant quotient section maps to its image under `systemComparison`; compatibility
of the limit map with its projections proves scalar balancing. Naturality and the
normalization at tensor generators prove existence and uniqueness.

The three proofs already landed by K4 are retained from the current shared source.
No new import or definition repair is needed. Searches from the retained attempt
and the current Loogle lookup found no existing reduction theorem that directly
matches this coefficient interface.

## Proved and sorry left

Closed 2 of the current 4 holes:
`AlgebraicGeometry.Scheme.CompletedConstantReduction.reduction_exists` and
`AlgebraicGeometry.Scheme.CompletedConstantReduction.finiteReduction_exists`.
Added 0 holes and split off 0 statements.

Two original holes remain, each attached to
`lem-weil-pbc-completed-constant-sheaf-reduction`:

- `AlgebraicGeometry.Scheme.CompletedConstantReduction.completed_constant_sheaf_reduction`:
  the sectionwise inverse-limit flatness, ordinary reduction isomorphism, exactness,
  and finite-projective retract argument remain to be assembled.
- `AlgebraicGeometry.Scheme.CompletedConstantReduction.finite_coefficient_identification`:
  the constant-to-function sheaf comparison and transport of the reductions.

## No longer needed

None. All original proof-dependency imports are retained for the two unresolved
original theorems. No node, module, or unit-level step is pruned.

## Where the brief, the DAG or earlier work was wrong

The retained report counted three proofs that K4 had already landed before this
session; those are not counted as new progress. The actual baseline is four holes.
The saved reduction attempt needed explicit universe parameters and explicit
presheaf/target parameters at the sheafification equivalence. Inferred parameters
caused expensive unfolding; specifying them avoids that cost without changing any
definition. Some compile requests received no server answer and were retried.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
