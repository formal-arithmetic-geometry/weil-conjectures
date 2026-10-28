## What changed

Proved `WeilConjectures.PurCompactSupport.reductionComparison_isIso` in
`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`. For positive exponent,
apply the canonical completed-to-finite proper quotient mate to the completed
open extension, use the already proved open coefficient comparison, and combine
them with `comparison_factorization`. No existing statement or definition changed. Two local unused-variable linter
options retain its exact original signature although the proof needs fewer
hypotheses.

Added the proof-only import `Sheaf.Paper.CompletedQuotientProperMate`. Its public
`WeilConjectures.completedQuotientProperMate` is fully proved. The lower
normalization argument reuses the complete private `quotient_proper_mate`
argument in `QcqsCompactSupportFiniteMates`, in an acyclic module. It identifies
the restriction square on sections, identifies its derived normalization on
K-injectives, transports the quotient projection formula through scalar
adjunctions, and substitutes the prescribed quotient coefficient maps. All its
supporting declarations are private and proved.

The parent node records this argument and its dependency. The new theorem
allows any compatible square witness with the canonical quotient components;
proof irrelevance identifies it with the normalized square. Exponent zero is
excluded by the original positivity hypothesis. The proof applies to zero
objects, arbitrary shifts and unbounded inputs, and adds no Tor, geometric or
constructibility hypothesis to the existing statement.

## Proved and sorry left

Closed one of the ten original holes:
`WeilConjectures.PurCompactSupport.reductionComparison_isIso`.
Added zero holes and split off zero unproved statements. The new lower theorem
`WeilConjectures.completedQuotientProperMate` has a complete proof.

Nine original holes remain, all attached to
`lem-pur-compact-support-integral-coefficient-comparison`:

- `WeilConjectures.PurCompactSupport.comparison_composition`
- `WeilConjectures.PurCompactSupport.comparison_identity`
- `WeilConjectures.PurCompactSupport.integralCoefficientComparison`
- `WeilConjectures.PurCompactSupport.recordedIdentification_existsUnique`
- `WeilConjectures.PurCompactSupport.refinementProperOpen_existsUnique`
- `WeilConjectures.PurCompactSupport.comparison_refinement`
- `WeilConjectures.PurCompactSupport.refinementComparison_coherence`
- `WeilConjectures.PurCompactSupport.comparison_strict_towers`
- `WeilConjectures.PurCompactSupport.comparison_projection`

## No longer needed

None. No existing import, node, module or unit step is withdrawn. The remaining
parent obligations retain their routes. The reduction proof uses the quotient
projection formula rather than the disputed generic arbitrary-coefficient
`finiteProperComparison_isIso`; it uses only the `finiteProperComparison`
definition from that module. This is not a claim that the whole module or any
other parent dependency can be pruned.

## Where the brief, the DAG or earlier work was wrong

Several planned coefficient-comparison auxiliaries import this item, so importing
them here would create a cycle. The existing private quotient-mate proof in
`QcqsCompactSupportFiniteMates` already supplies the actual proper factor needed
for reduction, but that consumer cannot be imported here either. Reusing its
lower argument in a separate module avoids both cycles. The original statement
and the unit route are preserved. No source-library declaration is changed.

## New nodes

`lem-pur-completed-quotient-proper-mate` records the fully proved theorem
`WeilConjectures.completedQuotientProperMate` in
`Sheaf.Paper.CompletedQuotientProperMate`. Its three proof steps are restriction
normalization, derived uniqueness on K-injectives, and transport of the quotient
projection formula to the actual scalar mate. Its source is the finite-quotient
proper/open argument in the current blueprint, Bhatt--Scholze Lemmas 6.7.7 and
6.1.13, and Stacks Tag 0GL6. This is a proved intermediate result, not a new
proof obligation. No change record is needed: only this item, its own node and
the new module/node are changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompletedQuotientProperMate": "c63642d63bfe987f91a7cbda13390ce100d53b81", "Sheaf.Paper.IntegralCompactSupportCoefficientComparison": "23bb6fd191ed47b9c91e6c10f5797d997dc4474e"}, "results": {}, "time": "2026-10-28T10:45:41+0800", "transitive": 0, "version": 1}
```

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
