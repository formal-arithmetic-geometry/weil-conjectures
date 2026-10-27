## What changed

Reduced `WeilConjectures.PurityFiniteSetting.line_zero_class_etale_realization` to
existing Cartier realization and divisor-class uniqueness, two narrower comparison
statements, and a proved private naturality calculation. Existing public signatures
are unchanged. Twelve comparison and endpoint definitions reuse definitionally equal named generic
closed-section constructions. Their precise before/after bodies and the new public
import are recorded in `coord/changes/B5-line-zero-closed-section-reuse.md`.

`ComparisonImageClosedSectionNormalization` constructs the source maps explicitly
and states their normalization for comparison-image constants. It has no Cartier
class, target object or final tau equation. `CartierSupportedComparisonSquare`
states only the supported Cartier arrow's exact-single comparison square; it has
no compact support or source normalization. The item specializes these statements,
then its naturality proof obtains the final equality for the actual tau map.

## Proved and sorry left

Closed the original hole of
`WeilConjectures.PurityFiniteSetting.line_zero_class_etale_realization` by a complete
reduction. The existing geometric theorem stays proved. The class identification
and local equations use `relativeCartierKummer_realization`, `divisor_class` and
uniqueness of `generalDivisorEtaleClasses`. The final tau equation follows from
proved naturality and inverse cancellation; no invertibility of the class is used.

Added exactly two holes, each in its own new module:

- `WeilConjectures.PurityFiniteSetting.comparisonImage_closed_section_normalization`,
  node `lem-pur-comparison-image-closed-section-normalization`.
- `WeilConjectures.PurityFiniteSetting.cartierSupported_comparison_square`,
  node `lem-pur-cartier-supported-comparison-square`.

The item module has zero remaining holes. Each new module has one named theorem
with proof exactly `by sorry`, its source and a complete proof in words. No data
definition contains a hole. One original hole closed and two narrower holes added
is a decomposition, with net minus one by hole count; it is not reported as a proof
of the full original statement without dependencies.

## No longer needed

No existing declaration, module or blueprint unit step is withdrawn. No globally
pruned module is claimed. The entire map-and-witness conclusion of
`lem-pur-closed-section-compact-origin` is no longer applied directly by the item:
its final map equality is proved by naturality. That node remains a proof dependency
of the source-normalization split, so it remains needed in the closure.

Finite-Tate and ordinary-Kummer work is supplied by the existing
`lem-pur-cartier-relative-kummer-realization`. No duplicate lemmas for that work are
introduced. The inherited maintainer `tool_uses` approvals are retained.

## Where the brief, the DAG or earlier work was wrong

The planned application of `closed_section_compact_origin` is not definitional:
it uses standard pro-etale constants, while the item's `P.constant` is the comparison
inverse image of etale constants. Its source maps also retain candidate comparisons.
The new source lemma records the canonical coefficient-unit transport, including
cancellation of those comparisons. This is an interface mismatch, not a disputed
mathematical statement.

The supported square is definitionally the published Hom comparison, but its
concrete instance and derived-category conversions exceeded the per-file time limit
in direct proofs. A generic exact-functor cancellation helper was proved in scratch;
the specialized API equation is documented as a separate strictly smaller step.
No statement was weakened to avoid that conversion.

Edge cases checked in words: identity section, empty base, zero class and coefficient
objects, arbitrary signed twist index for the generic cancellation, and ramified
finite coefficient levels. No class arrow is cancelled as an isomorphism.

The downstream usage audit found zero modules importing the item and all textual
uses of the twelve refactored declarations only in the item. Definitionally equal
reuse requires no consumer adaptation and does not change any target's meaning.

## New nodes

`lem-pur-comparison-image-closed-section-normalization` is the compact-source clause
of current blueprint rank-one Thom proof Step 1, generalized to a closed section.
It has exact canonical source definitions, an exact Lean statement and searches.

`lem-pur-cartier-supported-comparison-square` is the supported-arrow clause alone,
generalized to an effective Cartier divisor. Its proof in words is source-isomorphism
cancellation followed by exact-single and shift comparison. Both nodes are in
`sec-smooth-purity`, unit `sk-prop-an`; neither restates the six-conjunct item.

Definition reuse change record: `coord/changes/B5-line-zero-closed-section-reuse.md`.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
