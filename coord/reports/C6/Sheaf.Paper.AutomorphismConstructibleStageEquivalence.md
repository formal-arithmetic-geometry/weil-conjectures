## What changed

Proved `WeilConjectures.automorphismConstructibleStage_integral_coherence` in
`Sheaf.Paper.AutomorphismConstructibleStageEquivalence`, keeping every existing
public signature and public import unchanged. The proof uses the supplied
`IntegralComparisonCompositionLaws` and the specified components of
`automorphismStageIntegralSquare`.

Six proved private helpers handle transport of the compositor in either
argument, explicitly typed forward and reversed associativity, horizontal pasting
of two squares, and the identity square. Three associativity equations paste the
squares. Specializing to an automorphism and its inverse, cancelling the two
inverse compositors, and applying the unit equations proves the required actual
integral inverse and identity equations. Separate finite reductions are not used
to detect equality of morphisms.

Added the proved module `Sheaf.Paper.CommonStagePullbackRepresentativeLinearity`
and a private proof import of it. The new module exposes the explicit canonical
finite-stage linear-structure cache needed to elaborate its representative formula. The existing
`automorphismConstructibleStage_qbar_linear` specializes its generic theorem to
the already proved finite-stage rational linearity. The helper proves the scalar
identity for conjugated finite-stage arrows and transports it through `ofHom` by
congruence. It uses the literal coefficient expression and locally restricts
unfolding of the representative constructors. This preserves the original proof
argument while isolating the remaining expensive quotient matching calculation.

Validation: `lcompile.py --all` compiled both delivery modules successfully,
with no errors or warnings. All existing declaration signatures are unchanged.

## Proved and sorry left

Closed one of the item's five original holes:
`WeilConjectures.automorphismConstructibleStage_integral_coherence`.
Added no holes and no split-off sorry statements.

Also proved the new generic helper
`WeilConjectures.commonStageDerivedPullback_map_smul_of_linear`, attached to
`lem-sf-common-stage-pullback-representative-linearity`.
The previously proved common-stage linearity theorem remains proved.

The four untouched holes, all attached to
`lem-sf-automorphism-constructible-stage-equivalence`, are:

- `WeilConjectures.automorphismStageQbarSquare_existsUnique`;
- `WeilConjectures.automorphismConstructibleStage_integral_shifts`;
- `WeilConjectures.automorphismConstructibleStage_descended_shifts`;
- `WeilConjectures.automorphismConstructibleStage_inverse_comparisons`.

## No longer needed

None. No imports are removed. The remaining clauses and existing proofs retain
their recorded dependency route; no module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The recorded realized associativity law uses an equality transport whose direction
is accepted through definitional associativity of scheme composition. Rewriting
that expression can produce terms that do not type-check at tactic transparency.
A private proved restatement gives the transport explicit endpoints; the public
composition law is unchanged. No mathematical correction was needed. This
implements the integral coherence part of the existing sixth proof step directly
from the supplied composition laws.

The existing linearity calculation unfolded large common-stage types during
matching. After localizing its scalar calculation and removing a coefficient
type alias, the combined item still narrowly exceeded 60 seconds. The proved
representative-linearity calculation is therefore checked in its own module.
There is no change of definition, existing statement, or unit route.

## New nodes

`lem-sf-common-stage-pullback-representative-linearity` records the proved scalar
formula for actual common-stage pullback representatives, assuming rational
linearity in the selected coefficient field. Its stage-linear instance is the
canonical `ScalarLocalization.linear` construction, with no chosen or unknown data. It is a generic part of the existing
common-stage linearity argument and has no sorry. Its source is the
Weil-structures paragraph, original proof step 9; it keeps the existing unit route.
No change record is needed: existing definitions and signatures are unchanged.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
