## What changed

Proved `AlgebraicGeometry.Scheme.Modules.gradedLineFraction_overlap` by local affine-base
refinement, comparison over a fixed affine base, and the pullback universal property.
Its declaration signature and public imports are unchanged.

Added two proved supporting modules. `GradedLineFractionBaseRefinement` constructs the
localization map for a restricted chart and verifies its source and relative-Proj target
equations. `GradedLineFractionSameBase` constructs the homogeneous coefficient ring maps,
identifies the given fraction charts with `Proj.fromOfGlobalSections` on common affine
neighborhoods, and applies the existing unit-power invariance theorem to compare frames.
The coefficient ring maps are actual `DirectSum` constructions, not arbitrary witnesses
chosen from an unproved existence assertion. All proof helpers are proved and private.

The fixed-base proof uses the already proved
`Proj.fromOfGlobalSections_eq_of_unit_pow_mul` from
`WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`. The ordinary
localization maps, homogeneous-fraction surjectivity, affine adjunction, and standard
Proj transition maps also come from the existing library and Mathlib. Every use of
cancellation is by a free frame or by a unit denominator. Empty overlaps, unequal positive
denominator degrees, zero divisors, and nilpotents require no extra hypotheses.

The two new nodes and the original node record this proof route. No existing definition,
instance, declaration signature, public import, or global attribute is changed.

## Proved and sorry left

Original holes closed: 1 of 1, namely
`AlgebraicGeometry.Scheme.Modules.gradedLineFraction_overlap`.

New proved supporting declarations:

- `AlgebraicGeometry.Scheme.Modules.gradedLineFraction_baseRefinement`.
- `AlgebraicGeometry.Scheme.Modules.gradedLineFraction_sameBase`.

Holes added: 0. No `sorry` remains in the delivered modules. This is a proof, rather
than a decomposition into new unproved obligations.

Validation: remote `lcompile.py` passed all three delivered modules with no holes and
with the default heartbeat budget. The cleaned supporting modules compiled in 18.7 s
and 32.9 s; the final overlap module compiled in 4.6 s. All are below the 60 s limit.
The original theorem signature and public imports were compared with the current
source and are identical. The original node changes only `proof`, `proof_deps`, and
`proof_origin`; both new node signatures match their Lean declarations. The required
compilation, axiom and delivery preflight checks are run by `deliver3.py` before it pushes.

## No longer needed

No existing node or module is withdrawn or globally pruned. The declared dependencies
for relative graded line maps, local free generators, homogeneous localization, Proj,
relative-Proj transitions, and scheme morphism locality remain used through the two
supporting modules. The original module now imports those supporting proofs privately.

The planned explicit product-denominator comparison is unnecessary: the proved
`fromOfGlobalSections` unit-power invariance theorem supplies precisely that comparison.
No import was added for a separate product-denominator argument. Removed redundant
proof imports of `Mathlib.AlgebraicGeometry.Gluing`,
`Mathlib.Algebra.DirectSum.Algebra`, and
`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`: the existing public chart
interface already exports the declarations they supplied. The existing source
library and all unit-realizing declarations remain intact.

## Where the brief, the DAG or earlier work was wrong

The statement is correct, including its lack of a global generation assumption. The
original DAG describes a valid argument. Its product-denominator step can be replaced
by an existing proved Proj invariance theorem after constructing and comparing the
coefficient ring maps. No disputed statement or interface repair was required.

## New nodes

- `lem-trf-graded-line-fraction-base-refinement`: local restriction of a single chart,
  retaining its restricted frame, degree, and denominator; proved.
- `lem-trf-graded-line-fraction-same-base`: overlap comparison with a common affine base,
  allowing different source opens, frames, and positive degrees; proved.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
