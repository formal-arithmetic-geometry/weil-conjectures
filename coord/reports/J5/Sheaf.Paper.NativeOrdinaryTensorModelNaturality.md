## What changed

Filled `native_ordinary_tensor_model_naturality_kflat` in
`Sheaf.Paper.NativeOrdinaryTensorModelNaturality` without changing its statement.
Added proved private helpers for inverse-transpose naturality and the normalization
identity on actual chain maps into a K-injective. Reused the already proved private
chain-level currying equivalence, its component formula, and its naturality from
`Sheaf.Paper.NativeOrdinaryRepresentativeCurrying` through a proof-only `import all`.
Added a proof-only import of the Grothendieck K-injective resolution theorem.
Preserved the supplied forall-binder names, with a theorem-local unused-variable
lint setting for the two K-flat hypotheses used only in the proof.
Updated the item's DAG proof and dependencies to match this argument.

The square is tested against a K-injective resolution of its target total tensor.
Normalization identifies the resulting arrows with inverse transposes;
chain-level currying and `R.naturality` identify their curried arrows. The localized
resolution map is an isomorphism and can be cancelled. This construction uses no
choice of a tensor model and works for zero complexes and the empty scheme.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.native_ordinary_tensor_model_naturality_kflat`
(node `lem-sf-native-weil-tensor-ringed-derived-square-ordinary-naturality`).
No holes added, no statements split off, and zero `sorry` declarations remain in
the delivered module. The private adjunction and both private theorem helpers have complete bodies.

Validation: warning-free single-file compilation passed for the delivered module
(23.1 seconds) and its unchanged direct consumer,
`Sheaf.Paper.NativeWeilTensorRingedDerivedSquareOrdinary` (12.3 seconds), in import
order against the sandbox overlay. The compiler supplied the consumer's current
unpublished resolution-extension dependency in its private overlay. The temporary
unchanged consumer source was removed after this check. The theorem signature is
verbatim unchanged; all Lean lines are at most 100 characters.

## No longer needed

No imports removed, no modules withdrawn, and no existing dependency nodes pruned.
The original node had no declared proof dependencies; the proof reuses existing
currying and K-injective resolution results rather than introducing more obligations.

## Where the brief, the DAG or earlier work was wrong

The original DAG step omitted how to test the derived naturality equation and why
normalization applies to that test. A K-injective resolution of the target total
complex supplies an actual chain map for this purpose. Uniqueness from the total
coproduct inclusions identifies the normalization witness, and cancellation of the
localized quasi-isomorphism finishes the proof. The previously implemented native
currying calculation already supplies the needed sign and naturality identities.

Searches: Lean Finder returned general total-tensor naturality declarations;
Loogle found `Adjunction.homEquiv_naturality_left_symm`; the launcher grep found no
exact match. Local searches found `NativeCurrying.internalHomEquiv_naturality`
and `NativeCurrying.uncurry_component`, which are the proof's chain-level inputs.
No unit statement or unit route is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeOrdinaryTensorModelNaturality": "77e6b31d3fcba7b416bcb91d589a8d6c99e46787"}, "results": {"Sheaf.Paper.NativeWeilTensorRingedDerivedSquareOrdinary": {"hash": "ff7c1fed7a1304082dcf2503aa6bca2861d25814", "status": "OK"}}, "seconds": 90, "time": "2026-10-28T05:14:25+0800", "transitive": 0, "version": 1}
```

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
