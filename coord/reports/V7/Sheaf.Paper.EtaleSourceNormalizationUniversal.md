## What changed

Filled `AlgebraicGeometry.Scheme.etaleSourceNormalization_universal` in
`Sheaf.Paper.EtaleSourceNormalizationUniversal`. The original public statement and
public import are unchanged. Proof imports add `Sheaf.Paper.WitnessCompatibility`
(with access to its proved private comparison helpers), the source-library etale
flat-pullback instance, and Mathlib's adjunction/structured-arrow correspondence.

A private typed wrapper retains exactly the canonical `normalizationPullbackIso`.
Two proved private helpers specialize the existing generic flat-resolution mate
comparison to that isomorphism, and transport a universal structured arrow along
an invertible scalar mate. The ordinary mate is the identity
by its definition, so no equality between independently chosen tensor comparisons
is needed. The final proof applies this transport to the specified arrow.

Updated the item's own DAG proof, proof dependencies and proof origin to this route.
No other existing module or node is changed; no interface repair is required.

## Proved and sorry left

Closed the original single hole in
`AlgebraicGeometry.Scheme.etaleSourceNormalization_universal`.
No holes are added or split off, and none remain in the delivered module.
Both private helpers are fully proved.

Validation: the cleaned proof compiled through `lcompile.py` in 13.5 seconds,
with no warnings. `#print axioms` lists exactly `propext`, `Classical.choice` and
`Quot.sound`; there is no transitive `sorryAx`. The temporary axiom-print command
was removed before delivery. The theorem signature and original public import were
checked textually against the assigned source and are identical. Only the three
permitted proof-route fields of the existing DAG node change.

## No longer needed

No imports are removed and no modules are withdrawn. The original public import
supplies the statement's definitions and is retained.

Removed `def-weil-pbc-etale-universal-normalization` from this node's proof
dependencies: the proof directly establishes universality and does not invoke that
packaging predicate. The remaining original dependencies define the exact functors
and arrows used in the statement. The unit route is unchanged.

No new K-flat resolution or tensor-comparison obligations are needed: the proved
generic machinery in `WitnessCompatibility` already supplies them.

## Where the brief, the DAG or earlier work was wrong

The planned mathematics is valid, but the DAG's two steps cite only definitions
and omit the existing proved generic normalized derived-adjunction and flat-mate
machinery. Those results close the obligation without further splitting.
The nearby `DerivedScalarRestrictionPullbackMate` module cannot itself be imported
because it reaches this item through its parent chain; applying the acyclic generic
machinery directly avoids that cycle. Empty etale sources and zero coefficient
rings require no additional hypothesis in either generic argument.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.EtaleSourceNormalizationUniversal": "6fc97f0613c518ab890369924f66e90a2e60672d"}, "results": {"Sheaf.Paper.LisseTowerScalarRestriction": {"hash": "46d6b2cfbf39ba1725dc5b9bd1fed1feb111fe4c", "status": "OK"}}, "seconds": 128, "time": "2026-10-28T10:34:05+0800", "transitive": 0, "version": 1}
```

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
