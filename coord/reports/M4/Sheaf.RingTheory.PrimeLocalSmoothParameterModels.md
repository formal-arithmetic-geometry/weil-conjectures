## What changed

Replaced the sole hole in `IsLocalRing.exists_prime_local_smooth_parameter_models`
without changing its statement, universes, binders, or public imports. The proof enumerates a
minimal generating set of the maximal ideal, obtains its regularity from the existing
regular-local generator theorem, applies Popescu to the polynomial parameter map, and uses
Mathlib's directed partial-order final reindexing. A proved private functor restricts polynomial
algebras to the coefficient field while retaining their carriers and ring maps. Invertibility
of integer primes is proved by mapping their nonzero coefficient-field images.

Added `Sheaf.RingTheory.SmoothParameterQuotientDiagram` with a complete proof constructing the
quotient functor, quotient transformation, residue cocone, normalization equivalences, and
residue-field colimit. The quotient colimit proof explicitly constructs the universal map and
proves its factorization and uniqueness. Its geometric assertions use the single-stage lemma
below. Added the two residual algebraic statements in separate modules, and updated the item's
node and supplied nodes for all three new public statements. All four modules compiled through `lcompile.py` within the 60-second limit; the quotient
diagram took 5.4 seconds and the final item took 6.3 seconds. No existing module besides the
item is changed; no shared interface or source-library declaration is changed.

## Proved and sorry left

Closed the original hole in
`IsLocalRing.exists_prime_local_smooth_parameter_models`
(node `lem-per-prime-local-smooth-parameter-models`), by a complete assembly from the following
two strictly smaller residual statements. This is a decomposition, not a complete proof of
the mathematics: one original hole closed, two holes added, net minus one hole.

The only remaining holes in this delivery are:

- `IsLocalRing.prime_field_parameter_map_isRegular`
  (`Sheaf.RingTheory.PrimeFieldParameterRegularMap`,
  node `lem-per-prime-field-parameter-regular-map`): regularity of one fixed polynomial
  evaluation map. It asserts no smooth diagram, quotient diagram, colimit, or model existence.
- `IsLocalRing.smooth_polynomial_parameter_stage`
  (`Sheaf.RingTheory.SmoothPolynomialParameterStage`,
  node `lem-per-smooth-polynomial-parameter-stage`): the regularity, regular-sequence and
  quotient geometry of one supplied smooth polynomial algebra with nonzero origin fibre.
  It has no local target, completion, prime-field condition, approximation, or colimit.

`IsLocalRing.smooth_parameter_quotient_diagram` has no holes. Every private helper is proved;
there is no hole in a definition. Each residual theorem has its source, complete proof in
words, exact Lean statement, and node. Edge cases checked in the argument: d=0 gives an
empty parameter list and identity stage quotients; a zero stage quotient is explicitly excluded
and is excluded in the diagram by its map to the nonzero residue field; the universal property
allows a zero test ring. No perfectness of the residue field is assumed: only the prime field
is perfect in the regular-map step.

## No longer needed

The coefficient-coordinate route is unnecessary for choosing regular parameters: the existing
`IsRegularLocalRing.isRegular_and_quotients_of_generators` applies directly. Removed the item's
direct proof imports of `WeilConjectures.RingTheory.ExistsCoefficientSubring` and
`Sheaf.RingTheory.RegularCompleteCoefficientCoordinates`, and its proof dependencies
`lem-weil-pbc-cohen-coefficient-ring-exists` and
`lem-trf-regular-complete-coefficient-coordinates`. The completeness hypothesis of the original
statement remains unchanged; this argument does not use it directly.

Removed the direct proof import
`WeilConjectures.CategoryTheory.ExistsDirectedReindexing` and dependency
`lem-weil-pbc-filtered-category-directed-cofinal`: Mathlib's
`IsFiltered.exists_directed` already returns a partial order and final functor. The new proof
uses its existing Mathlib-leaf node `lem-weil-pbc-filtered-category-exists-directed-final`.
The old J × N poset replacement step and its cocone-comparison construction are unnecessary.

The following direct proof imports were also removed from the item because their argument now
belongs to a residual algebraic lemma, rather than the assembly:

- `WeilConjectures.RingTheory.PolynomialOriginRegularLocal`
- `WeilConjectures.RingTheory.FlatOverRegular`
- `WeilConjectures.RingTheory.CompleteLocalGRing`
- `WeilConjectures.RingTheory.FiniteTypeGRing`
- `WeilConjectures.RingTheory.GRing`
- `Mathlib.FieldTheory.PurelyInseparable.Basic`
- `WeilConjectures.RingTheory.RegularLocalMaximal`
- `Mathlib.RingTheory.RegularLocalRing.Polynomial`
- `WeilConjectures.RingTheory.RegularRingSmoothAscent`
- `Mathlib.RingTheory.Smooth.Flat`
- `Mathlib.RingTheory.RingHom.Flat`

Their mathematical dependencies remain explicitly recorded below the two residual nodes;
they are not claimed as pruned mathematics. The defining notions of regular schemes,
regular sequences, flatness and regular immersions remain statement or lower proof dependencies.
No module is withdrawn, and no claim is made that an upstream declaration or a module used by
another proof is globally unnecessary. The public imports of the existing item are preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan's coefficient-ring and power-series construction was more than needed to
prove regularity of a minimal parameter list. Its separate conversion from a directed preorder
to a poset was also unnecessary because the available Mathlib reindexing lemma is stronger.
No mathematical statement was weakened or marked disputed. The new regular-map lemma and the
new quotient-diagram lemma do not assume completeness of B, but the assigned statement keeps
all its original hypotheses. The fixed unit route is preserved; this is a reduction below
its realized statements and steps.

## New nodes

`lem-per-prime-field-parameter-regular-map` records original steps 2–4 as a fixed-map regularity
problem, using the existing origin-localization, regular-parameter flatness, G-ring and
closed-fibre criteria. It is a residual hole with no approximation conclusion.

`lem-per-smooth-polynomial-parameter-stage` records original steps 7–8 for one supplied smooth
polynomial algebra: flatness preserves coordinate regularity, smooth base change gives the
origin fibre, regularity ascends, and the affine quotient has regular equations of length d.
It is a residual hole with no diagram or local-ring approximation conclusion.

`lem-per-smooth-parameter-quotient-diagram` records the proved assembly of the quotient functor
and normalized residue colimit (original steps 7–9), using the single-stage lemma for its
geometric conjuncts. Its proof is complete. Initial delivery preflight found two truncated `lean.statement` records (extraction had stopped
at named arguments and cocone field assignments); those records were corrected to the full
unchanged signatures. No change record is needed because no existing
signature, definition, attribute, instance, or public import was changed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
