## What changed

This is a partial mathematical diagnosis and a proved construction, not a proof of the
original universal existence assertion. The original theorem and all existing signatures
are unchanged. Its single `sorry` remains, marked `STATEMENT-DISPUTED`.

In `Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization`:

- Constructed `normalizedIntegralLeft` by applying Mathlib's fully faithful
  `preimageIso` to the supplied ambient left realization followed by
  `sfQcqsCompactSupportRealization`.
- Proved its exact component equation and uniqueness. This completes the integral-left
  construction step for a comparison chosen by that construction.
- Added `TransportCoreData.normalizeIntegralLeft`, a concrete structure update, and
  proved its component normalization. It preserves every other data field.
- Proved that a normalization package forces the freely chosen `integralLeft` to equal
  that specific lift. A noncanonical comparison rules out the package.
- Proved the precise twist obstruction: replace just one field value by the canonical
  comparison followed by any nonidentity natural automorphism of its target functor.
  The resulting record still has type `TransportCoreData`, but admits no normalization
  package. Also proved the corresponding negation of universal existence, conditional
  on that nonidentity automorphism and a transport datum.

No arbitrary witness of an existence theorem is used to define new data. The preimage
is determined uniquely by the fully faithful map. No imported existence theorem for
transport laws is used in any new proof.

Searches were run through `msearch.py` (LeanSearch, LeanFinder, Loogle and grep).
Mathlib supplies the full-faithfulness APIs used here; it does not supply the asserted
normalization for arbitrary transport data. I read Zheng, Construction 5.25 and
Proposition 5.26, pp. 36–37, and the current blueprint unit. These construct induced
operations and specified comparisons; they do not normalize every freely chosen
comparison. No unit route was changed.

The interface-addition record is
`coord/changes/exceptional-integral-left-normalization.md`.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. Split-off holes: **0**.
This delivery is not counted as closing or decomposing the original hole.

The unchanged remaining hole is
`WeilConjectures.ExceptionalIntegralScalar.exists_exceptional_transport_core_normalization_laws`
(node `lem-sf-exceptional-ring-transport-core-normalization-laws`).

New proved theorems (all in namespace `WeilConjectures.ExceptionalIntegralScalar`):

- `normalizedIntegralLeft_hom`;
- `integralLeft_eq_normalized`;
- `TransportCoreData.normalizeIntegralLeft_hom`;
- `TransportCoreNormalizationLaws.integralLeft_eq`;
- `not_normalization_of_integralLeft_ne`;
- `not_normalization_of_integralLeft_twist`;
- `not_forall_normalization_of_integralLeft_twist`.

Their nodes are `lem-sf-exceptional-integral-left-normalization-lift` and
`lem-sf-exceptional-integral-left-normalization-obstruction`. The two accompanying
new definitions have complete bodies, with no holes.

Validation through `lcompile.py`: the complete item compiled in 10.6 seconds, with no
warnings. Its sole direct importer, `Sheaf.Paper.ExceptionalRingTransportCoreLaws`,
compiled unchanged in 8.4 seconds against this item, including current unpublished
system/evaluation dependencies. The unchanged importer copy was removed afterwards.
Temporary axiom probes checked all nine added declarations. Their axiom lists contain
`propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`: the prescribed
`sfCompactSupportFiniteIntegralFunctor`, `sfQcqsCompactSupportRealization` and even
`TransportCoreData` already depend on `sorryAx`. Thus this is not a claim that the
upstream import closure is proved. No new axiom or hole is introduced, and no original
law-existence theorem is invoked by the new proofs. The probes were removed.

## No longer needed

No import, existing node, or existing module is pruned. The only import remains
`public import Sheaf.Paper.ExceptionalRingTransportCoreData`. The new proofs use the
already available fully faithful inclusion and ambient compact-support realization.
No system/evaluation-law existence lemma is imported to conceal the quantifier defect.
The original DAG proof is not rewritten as a complete proof: no such proof is provided.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED`: the theorem quantifies over **every** `TransportCoreData d`.
That record contains `integralLeft` as unconstrained isomorphism data. Already its first
claimed normalization equation uniquely determines this field, as proved here. The
DAG's instruction to "retain" normalization from the realization does not constrain a
previously arbitrary isomorphism.

A concrete mathematical test is the identity compactification of a nonempty geometric
point, integral coefficients, and a rank-one free coefficient object. The identity
functor has the nonidentity natural automorphism minus identity: the valuation ring
has characteristic zero, including when l = 2. Replace the integral-left comparison by
its canonical value followed by this automorphism. All data-field requirements survive;
the first normalization equation does not. The Lean theorem proves the twist argument
for any supplied nonidentity automorphism; this delivery does **not** formalize that
specific geometric-point instantiation or claim an unconditional Lean refutation.
For empty schemes/zero functors the nonidentity-automorphism hypothesis need not hold,
which is why it is explicit in the proved obstruction. For the identity twist the
canonical component equation is the positive theorem proved here.

The required repair is to construct data and laws jointly, fixing comparison maps by
the actual proper/open reconstruction formulas. It must also address the analogous
arbitrary choices of `realizeF`, reconstruction, and system operations before asserting
the final system equation. Adding the desired equations as hypotheses, or moving the
same package to another `sorry`, would not prove the construction. I have not made that
change across other workers' modules or claimed it complete. The proved canonical lift
is available for that repair. Existing theorem/structure signatures and target
statements remain untouched.

## New nodes

`lem-sf-exceptional-integral-left-normalization-lift` records the complete canonical
lift, its component equation and uniqueness, and the corresponding concrete data
update. It has no `sorry`.

`lem-sf-exceptional-integral-left-normalization-obstruction` records the complete
uniqueness consequence and twist obstruction, including the explicitly conditional
negation of universal normalization. It has no `sorry`. Neither node creates another
pending version of the original package.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRingTransportCoreLawsNormalization": "30d30a6c6df80b01386b1bf09686cc0f84e44866"}, "results": {"Sheaf.Paper.ExceptionalRingTransportCoreLaws": {"hash": "b259262fe74d3b4e12841ffc4857a6dfbe5aca00", "status": "OK"}}, "seconds": 95, "time": "2026-10-28T08:03:14+0800", "transitive": 0, "version": 1}
```

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
