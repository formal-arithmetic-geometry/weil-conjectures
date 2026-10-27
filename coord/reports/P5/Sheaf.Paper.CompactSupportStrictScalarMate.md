## What changed

Only `lean/Sheaf/Paper/CompactSupportStrictScalarMate.lean` changes in Lean.
The baseline is the current A9 landing, which already closed nine earlier holes;
this packet preserves those proofs and closes three of its eleven remaining holes.

* `ordinaryOpenTensor_isIso`: identify the strict-tower map, componentwise, with
  postcomposition of `ordinaryBaseOpenTensor`. Functoriality preserves its isomorphism.
* `openTensor_ordinary`: the exact derived mate unit formula identifies the localized
  ordinary open map with the specified strict scalar mate. A proved private helper
  identifies the exact derived scalar adjunction with the right-derived adjunction
  transported along the canonical exactness isomorphism, by equality of their units.
* `open_base_ordinary`: apply the same argument on the base sites, using
  `finiteScalar_exact` and the existing `pulledBasis`. A proved private categorical
  helper transports inverse mates along `leftAdjointUniq`, using its unit formula
  and naturality of the restriction square. This yields exactly the prescribed
  `baseOpenExactNormalization`, including both universal scalar normalizations.

The only added import is the private proof import
`import all Sheaf.AlgebraicGeometry.VaryingRingOperations`, for its proved generic
exact-adjunction and exact-derived-mate helpers. Public imports and signatures stay
unchanged. The private helper `exact_of_tower` also makes the existing proofs of
`ordinaryPositiveRestriction_exact` and `baseTensor_exact` compare abstract functors
before specializing to sheaf categories; this avoids unfolding the large coefficient
constructions while proving the same exactness assertions. The existing proof of
`ordinaryBaseOpenTensor_isIso` is likewise factored through a proved private
abstract double-mate isomorphism lemma to avoid unfolding the site-specific
adjunctions; its mathematical argument remains iterated conjugation.

The existing node `lem-pur-compact-support-strict-scalar-mate` has its fifth proof
step and proof-origin note updated, and records `def-sp-varying-ring-operations`
as the generic exact-localization dependency. No unit route changes.

## Proved and sorry left

Closed three existing holes, all in namespace `WeilConjectures.PurStrictScalar`:

* `ordinaryOpenTensor_isIso`
* `openTensor_ordinary`
* `open_base_ordinary`

Added zero holes and split off zero statements. Eight holes remain unchanged,
all attached to `lem-pur-compact-support-strict-scalar-mate`:

* `WeilConjectures.PurStrictScalar.evaluationRestriction_existsUnique`
* `WeilConjectures.PurStrictScalar.finiteOrdinaryBalancing_existsUnique`
* `WeilConjectures.PurStrictScalar.finiteBalancing_existsUnique`
* `WeilConjectures.PurStrictScalar.factors_isIso`
* `WeilConjectures.PurStrictScalar.pulledBasis_existsUnique`
* `WeilConjectures.PurStrictScalar.proper_biproduct`
* `WeilConjectures.PurStrictScalar.strictProper_biproduct`
* `WeilConjectures.PurStrictScalar.compactSupportStrictScalarMate`

The finite base-site proof intentionally uses the already stated
`pulledBasis_existsUnique` through `pulledBasis`; proving this dependency remains
separate work. No new data are chosen from an existence theorem.

## No longer needed

No existing imports, modules or nodes are withdrawn. The three open-map proofs use
categorical inverse mates and exact localization, so they do not require a new
sectionwise tensor construction or new intermediate statements. Other dependencies
remain recorded for the eight unfinished obligations; no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The starting item was concurrently updated by A9. I refreshed it before writing the
final packet, preserving A9's nine closed holes; the denominator here is the eleven
holes of that refreshed source. The DAG's old fifth step described the three open-map
assertions as unproved. They are now proved by the pointwise and localization
arguments above. No false statement or interface repair is asserted.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
