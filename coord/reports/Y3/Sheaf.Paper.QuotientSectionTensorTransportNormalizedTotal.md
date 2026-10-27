## What changed

Repaired `section_tensor_transport_normalized_total`: `barB` must satisfy
`TensorSectionCondition a T c b barB`. The former arbitrary-isomorphism statement
cannot impose a fixed counit normalization. The sole caller,
`Sheaf.Paper.QuotientSectionTensorTransportNormalized` (unclaimed when checked),
now obtains a compatible `barB` from the proved `section_tensor_conjugate_exists`.
The caller's signature and public imports are unchanged. No target statement,
existing definition, or adopted source-library declaration changes.

The constructor conjugates `b` through the derived section equivalences and takes
the fully faithful preimage of that explicit natural isomorphism. The total proof
derives countable-colimit preservation of `c.model.E` from `c.ordinary`, constructs
the signed total with `mapBifunctorComparison`, and proves its summand formula.
It proves naturality of this total comparison, transfers the resolving conditions
through the counits of the termwise section equivalence, and transports the
internal-image equation to the supplied section complexes.

The internal-image equation is itself proved by pasting two separate evaluations
of the explicit `scalarTensorSectionPath` and cancelling the invertible
`scalarTensorSectionInput`. Both definitions are actual composites of existing
maps. The two evaluations are the remaining obligations: the left one uses the
normalized internal derived tensorator and has no ordinary map `e`; the right
one uses the ordinary scalar-unit formula and has no `b`, `barB`, K-flatness or
flat-term assumptions. Thus neither restates the original conclusion.

Compilation uses the server, one file at a time in import order. The main total
proof compiled in 47.9 seconds after replacing expensive concrete naturality
rewrites by a proved generic helper. All temporary profiler settings were removed.
Final compilation and the delivery's probe also check the adapted caller.

Change record: `coord/changes/Y3-quotient-section-total-conjugation.md`.

## Proved and sorry left

The item started with one hole, in
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport_normalized_total`.
Its repaired statement has a complete Lean proof from the two evaluations below.
This is a statement repair and decomposition, not a proof of the old false
statement or a claim of a net reduction in holes.

The new `section_tensor_conjugate_exists` and
`section_tensor_transport_internal_counit` have complete proof bodies, as do the
private transport and naturality helpers. The two new data definitions contain
no holes. The adapted parent retains its complete combining proof.

Exactly two holes are added, each the whole body of a named public theorem:

- `AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport_internal_left`
  in `Sheaf.Paper.QuotientSectionTensorTransportInternalLeft`, node
  `lem-sfb-quotient-section-tensor-transport-internal-left`.
- `AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_tensor_transport_internal_right`
  in `Sheaf.Paper.QuotientSectionTensorTransportInternalRight`, node
  `lem-sfb-quotient-section-tensor-transport-internal-right`.

There are zero holes in the item and two in the delivered files overall. No other
existing hole is removed or rewritten. The old `BarB` hole remains in its file,
but the adapted parent's route no longer requires it. Closure progress is left
to the project's pinned sorry ledger.

## No longer needed

The parent removes its private import of
`Sheaf.Paper.QuotientSectionTensorTransportNormalizedBarB` and its proof edge to
`lem-sfb-quotient-section-tensor-transport-normalized-barB`. The proved conjugation
constructor supplies the isomorphism together with the compatibility actually
needed. The existing BarB module, held by X3 when checked, is not edited or
withdrawn. The pure-map module held by Y2 is used unchanged.

The item's former direct proof dependencies are replaced:

- `lem-pur-kflat-total-tensor-model`, module
  `Sheaf.Algebra.Homology.KFlatTotalTensorModel`;
- `lem-weil-pbc-site-derived-tensor-descent`, module
  `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`;
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, module
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.

The explicit totalization and equivalence transport use the existing bifunctor
API instead of these broad direct proof obligations. Existing section tensor
normalization interfaces may still depend on them: no global withdrawal is
claimed. No module or declaration under `lean/WeilConjectures` is removed, and
no unit realization or unit route is bypassed. The unused bifunctor proof import
was removed from the new conjugation module before final compilation.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (former signature): `barB` was arbitrary. Take the identity
coefficient map with canonical scalar data over coefficients where `1 ≠ -1`.
Replace the canonical tensor comparison by its negative, leaving `c`, `b`, `e`
and the pure formula unchanged. On a nonzero flat regular complex in degree zero,
the old required equation changes sign on only its left side. The summand formula
already fixes the ordinary total map, so it cannot absorb this sign. The missing
condition is precisely the tensor-section conjugation square. Its existence is
proved here, and the original existential parent statement is preserved.

The original one-step plan did not distinguish the ordinary scalar-total square
from the derived tensorator calculation. The two new evaluation nodes do so and
meet at an explicit internal path. Their docstrings give complete source-based
proofs and address zero complexes and nonflat coefficient maps. In particular
the ordinary evaluation is valid for all internal complexes.

The inherited unit identifier `sk-thm-sfb-properbasechange` has no matching unit
file in this snapshot; the actual unit is `sk-thm-sfb-proper-base-change`. I read
that unit and its current blueprint section. No affected node realizes a fixed
unit step. The inherited identifier is retained in the new nodes rather than
editing maintainer-owned unit metadata.

Current server queue and error records were checked at the start: this item had
one proof hole and no listed repair or quarantine to restore. Text search,
direct-import search and `tools/downstream.py --uses` found only the adapted
parent as a consumer of the changed theorem.

## New nodes

`def-sfb-quotient-section-tensor-transport-internal-data`, in
`dag/nodes/sec-six-functors-basics/`, attaches the two explicit input/output-path
definitions in `Sheaf.Paper.QuotientSectionTensorTransportInternalData`.

`lem-sfb-quotient-section-tensor-transport-internal-left` attaches the derived-side
evaluation, whose only hole is its named theorem. It uses the conjugation and
representative normalization interfaces, independently of the ordinary map `e`.

`lem-sfb-quotient-section-tensor-transport-internal-right` attaches the ordinary
evaluation, whose only hole is its named theorem. It totalizes the scalar-unit
generator square and uses no normalized derived tensorator or resolving condition.

`lem-sfb-quotient-section-tensor-transport-internal-counit` attaches the proved
pasting and input-cancellation theorem used by the item.

`lem-sfb-quotient-section-tensor-conjugate` attaches the proved fully faithful
conjugation constructor used by the adapted parent. Each new node records actual
leansearch, loogle and grep searches. The item and parent nodes are updated to
match the delivered proof route, and the item's statement correction records its
sole citer. The change record is
`coord/changes/Y3-quotient-section-total-conjugation.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionTensorConjugate": "46304b0668345b0b47f03d972aab0bebf559b927", "Sheaf.Paper.QuotientSectionTensorTransportInternalCounit": "b46dbc485f7ddea063001f3c35ccf110e0e0f5dc", "Sheaf.Paper.QuotientSectionTensorTransportInternalData": "3b48c6434059a20923fd39c677768fa17bd316ed", "Sheaf.Paper.QuotientSectionTensorTransportInternalLeft": "4a379ed8f4ab417079f7dcf9c463b9a5e06e8d86", "Sheaf.Paper.QuotientSectionTensorTransportInternalRight": "0e45fe4e95de430a709e714169a751137fe5abcd", "Sheaf.Paper.QuotientSectionTensorTransportNormalized": "f10c0bdfed6b368813faccb57c9f42fc8840b991", "Sheaf.Paper.QuotientSectionTensorTransportNormalizedTotal": "08a7ae2b6fae9da0d06f552b343f104ef40f283a"}, "results": {"Sheaf.Paper.QuotientSectionTensorTransport": {"hash": "1da7cab05096327244e5569fecf71a173f2d050b", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T03:41:11+0800", "transitive": 0, "version": 1}
```

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
