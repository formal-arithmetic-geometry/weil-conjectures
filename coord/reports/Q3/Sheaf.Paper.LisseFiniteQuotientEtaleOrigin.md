## What changed

Split the deep existence proof into two strictly smaller public statements and assembled
those statements in the original theorem. `LisseFiniteQuotientEtaleOriginCore` carries
level descent, finite local constancy, vanishing, and refinement lissity. The transport
theorem carries only the conditional constant-model isomorphism. The original theorem
constructs the requested structure from the core witness and the transport theorem.

The three Lean modules compile in import order with `lcompile.py --all`.

## Proved and sorry left

The original theorem `AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin`
now has a complete proof by assembly. Its original one `sorry` is closed. Two strictly
smaller proof obligations are split off and remain as named public theorems:

- `AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_core`, node
  `lem-weil-pbc-lisse-finite-quotient-etale-origin-core`;
- `AlgebraicGeometry.Scheme.lisse_finite_quotient_etale_origin_transport`, node
  `lem-weil-pbc-lisse-finite-quotient-etale-origin-transport`.

Each split theorem has exactly one `sorry` as its whole proof. Holes closed: 1.
Holes added: 2. No `sorry` occurs inside a definition.

## No longer needed

The original proof's direct dependencies on finite-coefficient origin presentation,
finite-level comparison, bounded tower internals, completion evaluation, and pullback
coherence are now below the two split nodes. The item theorem imports only the core and
transport modules directly; those dependencies remain recorded on the split nodes and
are needed by the eventual proofs. No unrelated module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The prior node bundled two independent hard constructions: descent of the finite
quotient level and conditional transport of a supplied constant model. A direct proof
was not available in the current library. The split preserves the exact original
statement and makes each remaining obligation strictly simpler; the final structure
assembly is proved in Lean.

## New nodes

`lem-weil-pbc-lisse-finite-quotient-etale-origin-core` records the core descent theorem
and its source proof. `lem-weil-pbc-lisse-finite-quotient-etale-origin-transport` records
the conditional transport theorem and its source proof. Both node files are under
`dag/nodes/sec-proper-base-change/` in this sandbox.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteQuotientEtaleOrigin": "cf194cfc144c76044546ae2873a5578cc30d42e8", "Sheaf.Paper.LisseFiniteQuotientEtaleOriginCore": "bb951c5fc793332cdf3e5c71929799c215f0d999", "Sheaf.Paper.LisseFiniteQuotientEtaleOriginTransport": "71e4990fb446590a309b27d4852de82b5797a5c5"}, "results": {}, "time": "2026-10-27T23:52:56+0800", "transitive": 0, "version": 1}
```

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
