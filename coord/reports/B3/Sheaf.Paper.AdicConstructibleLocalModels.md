## What changed

Replaced `adicConstructible_localModels`'s hole with a proof preserving its statement.
The proof intersects the finitely many constructible cohomology stratifications, proves
that the strata are Noetherian, applies the existing proved lisse-residue lifting theorem,
pulls its covering sieve back along `AsSmall.up`, and composes the slice isomorphisms.

The remaining immersion, site-model and coefficient normalization is stated separately
as `sfbAdicImmersion_liftingInput`. This prepares a complete complex and its lisse residue
and compares slice categories; it asserts neither a covering nor a perfect local model.
The existing lifting theorem supplies those conclusions. The original unit route is retained.
No existing definition, public signature or public import was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.adicConstructible_localModels` (one of one original holes).

Added one hole, in the new public theorem
`AlgebraicGeometry.Scheme.sfbAdicImmersion_liftingInput`.
It is the only `sorry` left in this packet. This is a decomposition, not a completed
axiom-free proof; the net hole change is zero. The three private stratification and
Noetherian helpers are fully proved. There are no holes in definitions.

## No longer needed

No original imports were removed: the item initially had only its statement-data import.
The added proof imports are refinement, zero/constant sheaf facts, the lifting theorem
and the new transport lemma.

The main proof does not need `lem-sfb-adic-finite-stratification-pullback`
(`Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback`): the original residue is in
fixed-scalar sheaves and the proved refinement API already pulls it back to intersection
strata. It does not need `lem-sc-affine-noetherian-underlying-space`: Noetherian strata
follow directly from locally finite type immersions and Noetherian subspaces.
These dependencies were removed from this node's proof route, without withdrawing any
existing module or changing another consumer.

Completion-unit restriction, field tensor bounds and comparison pullback remain needed
in the new transport lemma's proof plan. They have not been pruned transitively.
The existing lisse-residue perfect-lifting theorem remains needed and is used directly.

## Where the brief, the DAG or earlier work was wrong

The former node's transport step requires actual comparisons between fixed-scalar
sheaves and constant-ring modules, between original and small sites, and between the
actual inverse-image completed ring and the canonical completed ring. Its existing
completion-unit and comparison declarations provide the mathematical ingredients,
but not one immediately applicable Lean statement in the required presentations.
The new node makes that remaining step explicit, with its source and full proof plan.

The original finite-Tor clause of `IsSfbAdicConstructible` is unnecessary for this
forward proof: the residue quotient is a field, so its bounded cohomology has the same
tensor bounds. This does not change the original predicate or theorem statement.

Edge cases checked in the argument: empty degree intervals are avoided by retaining
`a ≤ b`; degrees outside the interval use preservation of zero objects; empty schemes
and empty slice objects use the same exact equivalences and empty-cover sheaf axiom.
The transport lemma needs only maximality of I, not finite residue cardinality,
regularity of A, or perfectness of A/I over A.

## New nodes

`lem-sfb-adic-immersion-lifting-input`, module
`Sheaf.Paper.AdicImmersionLiftingInput`, records the missing immersion/site/coefficient
normalization step. Its conclusion is strictly a preparation for lisse-residue lifting:
it produces no covering sieve and no bounded finite-projective coefficient complex.
Its docstring and DAG proof specify the actual projection and constant-complex
comparisons, not arbitrary coefficient identifications.

Validation: both sandbox modules compiled together through `lcompile.py --all`
(17.3 seconds for the transport statement; 15.0 seconds for the main proof).
The original theorem signature was compared verbatim with the current repository
and is identical. Import-direction and DAG-reference checks passed.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
