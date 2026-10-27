## What changed

Filled three existing proofs in `Sheaf.Paper.RationalPurityPresentation` without changing any
public statement or public import. The Tate component definition is refactored through the
coherent natural isomorphism with exactly the same six factors; a private reflexivity lemma
checks equality with the old definition.

- `pbcPurityCoefficientChange_square`: identify the published coefficient pullback with the
  completed coefficient map, test both composites on every finite target projection, and use
  the existing finite coefficient-map naturality square.
- `pbcPurityTwistedScalar_naturality`: assemble the model comparisons into a natural
  isomorphism on the full lattice subcategory and cancel the fully faithful coefficient
  model. Compose this Tate comparison with shift interchange and completed-pullback scalar
  comparison. The integral-generator equation follows from this naturality using the existing
  `pbcScalarLocalization_naturality` square and the generator formula for linear transport. The generic localized-square proof uses the existing
  `rawScalar_naturality` helper, which clears a power-of-uniformizer denominator and cancels its
  invertible image to extend that equation to every rational arrow.
- `pbcPurityScalarNormalization_existsUnique`: invert the existing integral-normalized
  finite/raw scalar comparison. Its equality of integral tensor functors identifies the
  component endpoints; a proved private lemma transfers heterogeneous equality from homs to
  inverses. Every rational object is literally an integral representative, which gives
  uniqueness by extensionality. This includes identity inclusions.

Added proof imports with `import all` for the existing private quotient-normalization,
finite-square, tensor-Hom, and integral-tensor-identification helpers. The public import of
`IntegralCompactSupportUniformRestriction` is retained. Six new private lemmas (the
component equality, two integral-generator equations, localized-square naturality and two
generic inverse lemmas) are proved. A private scalar-lift record packages the existing
object map, rational Hom map, functor laws and integral-generator equation; its functor
uses exactly those supplied maps. The coherent Tate model is
one new public definition; there are no new holes or new unproved statements. Local irreducibility keeps the large stage
functor definitions from repeatedly unfolding in subsequent assertions.

The already-proved ordinary Tate-model bridge now reuses the existing private
`restrictionRoundTrip` instead of reconstructing identity restriction in this file.
Its identity-on-sections normalization and uniqueness proof are unchanged. The chosen
ordinary Tate model has its existing inferred return type written explicitly.

The already-proved `pbcPurityGeometricBounds` now reuses
`PurCompactSupport.coefficientPrimeUnit`, avoiding a duplicate characteristic/cardinality
argument. The node's Steps 1 and 3 and proof dependencies record these proofs. The existing
`def-zl-pbc-finite-raw-scalar-comparison` is used as a proved tool from another unit for the
same raw/stage normalization already required by this unit; it does not bypass the unit's
purity, coefficient-square, descent, or retract route. Its existing proof and private
integral-tensor-identification helper were read. No maintainer `tool_uses` approval was added
by the worker.

## Proved and sorry left

Closed three of the seven original holes, by fully qualified declaration name:

- `AlgebraicGeometry.Scheme.pbcPurityCoefficientChange_square`
- `AlgebraicGeometry.Scheme.pbcPurityTwistedScalar_naturality`
- `AlgebraicGeometry.Scheme.pbcPurityScalarNormalization_existsUnique`

Added zero holes and split off zero statements. The four original holes left unchanged are:

- `AlgebraicGeometry.Scheme.pbcPurityAmbientProperties`
- `AlgebraicGeometry.Scheme.pbcPurityCompactScalar_properties`
- `AlgebraicGeometry.Scheme.pbcPurityStageA_coherence`
- `AlgebraicGeometry.Scheme.rationalPurityTransitivitySummands`

All four remain attached to `prop-pur-rational-purity-transitivity-summands`, with their
existing source and full proof docstrings. The final purity theorem is not claimed proved.

## No longer needed

Removed the private import `Mathlib.Algebra.CharP.CharAndCard`: the geometric-bounds
proof now uses the existing coefficient-prime unit theorem instead of rebuilding its
characteristic argument. The ordinary Tate-model bridge no longer uses `pbcRestrictComp_exists` or reconstructs
the identity restriction isomorphism: it reuses the proved generic `restrictionRoundTrip`
from the same coefficient-presentation module. No modules, nodes, or unit steps are withdrawn. The remaining four holes
still need the recorded geometric preservation, compact-support scalar, associator, and
purity/descent arguments. The raw/stage normalization reuses an existing proved comparison
instead of duplicating its quotient-map and fraction-naturality construction.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The initial complete proof exceeded 60 seconds; the
coherent Tate model packages the large comparison once. Its exact definition refactor and
consumer check are recorded in `coord/changes/W3-rational-purity-coherent-tate-model.md`. The normalization hole already had an exact comparison
available in the library, in the opposite direction. Inverting it preserves the prescribed
integral normalization, including repeated stages.

The geometric assumptions and all existing public signatures are unchanged. The latest blueprint's
`sk-thm-purity-transport/_section.md` was checked: it still requires coefficient-compatible
smooth purity with the normalized adjunction. The partial proofs here preserve that route.

The server compiler has checked all three complete proofs and the component equality.
Development timing directives were removed; `deliver3.py` performs the final single-file
time-limit check and delivery preflight.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
