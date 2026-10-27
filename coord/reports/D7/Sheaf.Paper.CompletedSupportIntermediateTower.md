## What changed

`Sheaf.Paper.CompletedSupportIntermediateTower.reconstructionNormalization` is reduced to the
proper direct-image/quotient-unit subcalculation from step 4 of its existing proof plan.
The first normalization is proved by cancellation of the invertible reduced completion unit.
The second uses naturality of the completion unit, naturality of the prescribed
`directLimitIso`, and the mate/counit characterization of `properProjection`. A proved private
categorical lemma justifies cancellation after precomposition with a completion unit; it uses
invertibility of the completed unit and completeness of the target, rather than assuming the
original unit invertible. Target completeness is transported along the existing isomorphism
`mu` from `completionUnits`.

The new proof import is `Sheaf.Paper.SupportProperUnitNormalization`. Its theorem proves
only the proper-pushforward unit equation, without an open extension or compact-support object.
It uses the existing general mate-naturality lemma, `unit_mateEquiv`, and the identity between
iterated mates and the conjugate under composite adjunctions. The only split obligation is the
strict reduction/pullback augmentation square in `Sheaf.Paper.SupportReductionAugmentationPull`.
The parent node's proof records this implementation.
Local irreducibility attributes on the shared constant-section map and the existing finite
comparison definitions avoid unfolding their large chosen data during later proofs; their
bodies and signatures stay unchanged. No existing signature, definition body, public import, or target statement changes.

## Proved and sorry left

Original item: seven holes. Closed/reduced:
`AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.reconstructionNormalization`
(node `lem-cbc-completed-support-intermediate-tower`). Its two conclusions are proved by actual
Lean composition and cancellation from the smaller subcalculation and the existing helpers.
This is a decomposition, not a net hole closure: one original hole is replaced by one smaller
hole.

The six original holes left unchanged, all attached to
`lem-cbc-completed-support-intermediate-tower`, are:

- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.strictUnits`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.completionUnits`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.exchangeSubstitution`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.finiteUnits`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.twoSubstitutions`;
- `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower.strictFiniteCoherence`.

One new hole:
`AlgebraicGeometry.Scheme.OrderedExchange.supportReductionAugmentationPull`
(node `lem-cbc-support-reduction-augmentation-pull`). Its new module contains exactly that
named public theorem and a complete proof in words. The intermediate theorem
`AlgebraicGeometry.Scheme.OrderedExchange.supportProperUnitNormalization` is proved from it
by a strict mate-naturality calculation followed by the derived unit/mate equation.
No hole occurs in a definition or private helper.

## No longer needed

None. No existing imports, nodes, modules, or unit steps are removed. The unchanged remaining
obligations still need their recorded dependencies. No source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction is made. The proper-unit equation needed in the reconstruction
argument is stated explicitly in step 4 of the parent node, but the available normalization
interfaces use a different small-site/coefficient realization. The generic
`strictReductionProjectionCompletionUnit` was also found and read: it uses
`CategoryTheory.AdicSites.Site` and `ConstantCompletion.quotientPresentation`, whereas this
item fixes the original pro-etale site and `OrderedExchange.reductionData`. Thus its signature
is not the statement required here. The final split records only the strict augmentation square
for this prescribed realization. The proper-unit and reconstruction calculations are proved
from that square. No completeness or properness assumption is needed for the split square.

For edge cases, the zero complex and empty schemes give zero maps, the unit ideal gives the
zero quotient completion, and the zero ideal specializes to the diagonal comparison. None
requires cancellation of an arbitrary completion unit or faithfulness of derived evaluation.

## New nodes

`lem-cbc-support-reduction-augmentation-pull` in `sec-smooth-purity`, unit `sk-prop-sf-cbc`:
the prescribed strict reduction/pullback comparison preserves quotient insertion. Its proof
in words calculates the ordinary insertion, retains quotient transitions, and descends through
the normalized resolving-class model. Its proof records the existing flat-term K-flat resolution
and ringed-topos K-flat pullback lemmas as general tools; these are the representative facts
used by the prescribed model, and no alternative unit route is introduced. It is strictly smaller than the proper-unit equation and
the compact-support reconstruction. The small cases are listed above and in its docstring.

`lem-cbc-support-proper-unit-normalization` in the same chapter and unit: a proved intermediate
theorem identifying direct image of the completion unit under the specified limit comparison
with inverse limit of the projection mate after the target unit. It is proved by mate naturality,
unit compatibility, and functoriality from the first new node. Whole-blueprint searches for
"completion unit" and "quotient augmentation" found no matching blueprint statement; the nearest
ancestor is `thm-cbc-complete-proetale`. No change record is required because no existing
statement or definition is modified.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
