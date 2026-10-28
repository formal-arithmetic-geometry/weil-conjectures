## What changed

Repaired `native_integral_scalar_morphism_normalization` by constructing the normalized
natural morphism, its two outer isomorphisms, and its six component arrows together.
The old hypothesis supplied arbitrary outer isomorphisms, which cannot force the
prescribed component formula. The construction uses the stage inclusion comparison,
`rationalLeft`, localization of the integral linear action, the two integral
realizations, `sfQcqsCompactSupportRealization`, the scalar mate, and
`operationTransport`. Full faithfulness of derived sections lifts their natural
composite to the required native natural transformation.

Adapted only the proof of
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_integral_scalar_morphism`
to obtain the morphism and both component properties from this construction. Its
signature, `IntegralComponent`, `finiteSource`, and `finiteTarget` are unchanged.
Updated both DAG proof plans and recorded the correction of the disputed statement.
No source-library module or target statement is changed. The item replaces its
public import of the obsolete existence split with the compact-support data module;
its two proof imports supply the proved natural boundary comparisons and the derived
section equivalence. The finite-stage comparison module imports only its operation data
and the stage-system functor API. The boundary module contains the concrete natural
isomorphisms and their prescribed first-three-arrow and last-two-arrow formulas;
the item constructs and lifts their composite with the scalar mate.

Validation: all four delivered Lean files compile without warnings through
`lcompile.py --all`, in import order. The constructor and adapted caller took
37.2 s and 31.3 s. The two supporting modules passed separately within the 60 s
limit (12.1 s for the finite-stage comparison and 59.3 s for the boundaries).
The delivery tool performs its independent interface, consumer and axiom checks.

## Proved and sorry left

Holes closed: one, in
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_integral_scalar_morphism_normalization`.
Its corrected constructive statement has a complete proof. The false universal
statement about arbitrary factorizations is explicitly corrected, not claimed proved.
The parent's unchanged full statement has a complete proof from this construction.
The new finite-stage comparison,
`WeilConjectures.LocallyFiniteAdicCompactSupport.finiteStageAction_normalizedComparison`,
is proved in full, as is
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_integral_scalar_boundaries`.
Holes added: zero. No unfinished
intermediate statements are split off, and zero `sorry`
tokens remain in the delivered Lean files. All private helpers have complete proofs
or explicit constructions.

## No longer needed

The old route through
`lem-sf-native-integral-scalar-morphism-existence` and
`Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence` is unnecessary.
The canonical natural comparisons construct the morphism directly and retain the
normalization, so the weaker existence theorem is not used. Its module and node are
preserved; the module is held by K1 and is not modified. Its dependency is removed
from both delivered proof plans. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original split asserted that existence of some isomorphisms `b` and `d` in a
factorization forces their prescribed canonical component values. It does not:
negating a natural transformation and its left outer isomorphism preserves that
factorization in these additive categories. The fixed six-arrow formula keeps its
original sign. On the identity compactification and a nonzero rank-one
characteristic-zero coefficient object these are different maps. The old assertion
was already marked `STATEMENT-DISPUTED` in the source. The replacement constructs a
single normalized morphism instead of asserting normalization for every such morphism.
The sole citing parent keeps its full original statement and all definitions.

The current server queue lists this as a disputed stage-3 item, with one hole; no rework row or
build-error file was present. The parent module was unclaimed when checked on the
server; its proof alone is adapted. The unit record has no realized statement or
steps assigned to either of these auxiliary nodes. The current blueprint unit route
and Bhatt--Scholze Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15 are preserved.
The argument also covers zero objects and empty schemes and never assumes the
middle scalar comparison invertible.

## New nodes

`lem-sf-finite-stage-action-normalized-comparison`, in
`Sheaf.Paper.FiniteStageActionNormalizedComparison`, is the proved finite-stage
inclusion/comparison step and its component formula after any functor J. It uses
the existing identity-component stage inclusion isomorphism and equality transport.
It is strictly the first rational comparison step of the constructor, contains no
`sorry`, and introduces no unfinished obligation. Separating this general comparison
keeps its coefficient-category elaboration separate from the native construction.
The stage isomorphism used by the boundary construction comes from this fully proved
existence theorem.

`lem-sf-native-integral-scalar-boundaries`, in
`Sheaf.Paper.NativeCompactSupportIntegralScalarBoundaries`, proves the two natural
boundary isomorphisms and their separate component formulas. It does not take a
scalar mate and does not construct the lifted morphism; those steps and their
combination remain proved in the item. This separates an already proved part after
profiling the category conversions: the combined file passed with profiling but a
clean compile took 65 seconds. No compiler time limit was raised. All supporting
definitions are explicit constructions; all supporting theorems are proved.

Change record: `coord/changes/M4-native-integral-scalar-normalization.md`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteStageActionNormalizedComparison": "97c901fd8dc0ead7385ce65caed1ef344df72479", "Sheaf.Paper.NativeCompactSupportIntegralScalarBoundaries": "96a425ff4598ebf9a04d279408c2729ead477746", "Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism": "503a9bd548850f0de9900c59674defc29435e2fd", "Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization": "e5afc7470e0d81aa56bbfebbb16d710bd60b99aa"}, "results": {}, "time": "2026-10-28T09:24:36+0800", "transitive": 0, "version": 1}
```

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
