## What changed

Proved `WeilConjectures.AdicQbarRealization.exists_common_pullback_identity_unit`
without changing its signature. Only the assigned Lean module and its own DAG
node are changed. Three private proof imports provide the already stated
finite-stage equivalence, normalized common-stage descent, and naturality of
the specified compositor.

The shorter argument is categorical. Finite-stage identity pullbacks are full
and faithful by `isomorphismFieldTransportFiniteStage`. A private, fully proved
representative calculation lifts these properties through a stage-system
morphism: fullness uses conjugation and a finite-stage preimage; faithfulness
uses an eventual-equality witness and finite-stage injectivity. The actual
common-stage functor is this descent by `commonStagePullbackNormalizedDescent`.

`PodCoefficientDescent.common_compositor_existsUnique` supplies a natural
isomorphism with exactly the prescribed compositor components. Equality-only
object copies are identified with their original functors using that module's
proved private `commonPullback_eq` helper through a private `import all`. This
avoids unfolding the large chosen functor during elaboration. Mathlib's
`Functor.fullyFaithfulCancelRight` lifts the inverse compositor to `e : F ≅ Id`.
Its component formula gives `F(e_M) = c_M⁻¹`. Naturality of `e` at `e_M`, followed
by cancellation, gives `e_(FM) = F(e_M)`. Therefore the specified compositor
followed by `e_(FM)` is the identity, as required.

This uses the following existing nodes as tools of the identity-unit argument:
`lem-pod-isomorphism-field-transport-finite-stage`,
`lem-pod-common-stage-pullback-normalized-descent`, and
`lem-pod-reindexing-hom-coefficient-descent`. They supply exactly the native
functors and the prescribed natural compositor. No node of this unit supplies
these statements. The unit statement and its realization route are retained;
this only shortens the subargument below that route. Their dependency closures
were checked not to reach this item. No tool-approval metadata was edited.

Searches: leanfinder for idempotent equivalence functors, Loogle for
`CategoryTheory.Functor.preimage`, and Mathlib grep for fully faithful
cancellation. Loogle and local source inspection found the cancellation API.
The other hits were generic equivalence and preimage constructions; no exact
adic normalization theorem was found. All three searches are recorded in
`searches.jsonl`.

Validation: the complete delivered module compiles through `lcompile.py` in
9.1 seconds, with no errors or warnings. All three private imports are used.
A source comparison confirms the original theorem signature is unchanged, and
all Lean lines are at most 100 characters. Debugging probes are outside `lean/`
and are not part of the delivery.

## Proved and sorry left

Closed 1 existing hole:
`WeilConjectures.AdicQbarRealization.exists_common_pullback_identity_unit`
(node `lem-sf-adic-common-pullback-identity-unit`).

Added 0 holes; split off 0 statements. The assigned module has 0 remaining
`sorry`s. All five private helpers are proved. The proof uses existing stated
dependencies, including the existing compositor theorem, whose unproved
obligations remain with their current nodes and owners. This is a proof from
existing declarations, not an assertion that their entire axiom closure is
already sorry-free.

## No longer needed

No existing import was removed and no module was withdrawn. The public
`AdicRealizationFamilyData` import is preserved. The old planned proof
dependencies are not used directly and are removed from this node's
`proof_deps`:

- `lem-weil-proetale-isomorphism-inverse-image`
  (`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`);
- `lem-trf-integral-inverse-image-comparison-composition`
  (`Sheaf.Paper.IntegralInverseImageComparisonComposition`);
- `lem-pur-derived-pullback-tensor-iso`
  (`Sheaf.Paper.DerivedPullbackTensorIso`);
- `def-weil-rationalization-karoubi`
  (`Sheaf.Paper.SfRationalizationKaroubi`);
- `lem-weil-isomorphism-comparison-scalar-extension`
  (`Sheaf.Paper.IsomorphismComparisonScalarExtension`);
- `lem-pur-derived-pullback-tensor-constraints`
  (`Sheaf.Paper.DerivedPullbackTensorConstraints`).

The new proof does not construct a normalized integral identity or descend its
scalar equation: full faithfulness and the existing specified natural
compositor suffice. Several listed modules remain transitively imported by
existing interfaces or needed by other nodes. This report makes no claim that
those modules can be withdrawn globally. The common-stage coefficient
construction `def-weil-algebraically-closed-coefficients` is still used, as is
`def-weil-derived-pullback-tensor-hom` for the actual pullback object specification.

## Where the brief, the DAG or earlier work was wrong

The old proof plan was sufficient but longer than necessary: the required unit
is forced categorically by full faithfulness and the prescribed natural
compositor. No additional identity-normalization lemma is required.

An attempted specialization of a prime-to-characteristic geometric
transport theorem would introduce the extra hypothesis `l ≠ D.p`, which the
item does not assume. Instead, the proof obtains stalk units directly from
the supplied residue-field invertibility and applies the unrestricted
finite-stage transport theorem. Empty schemes therefore require no separate
case, and neither the theorem nor any shared definition is weakened.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicCommonPullbackIdentityUnit": "e2ff305df123d20c4af44687b4a1c387f6da6347"}, "results": {"Sheaf.Paper.AdicReindexingCore": {"hash": "1fbdf722b89e076b82fcc0dc369f866bd650b009", "status": "OK"}}, "seconds": 96, "time": "2026-10-28T05:27:44+0800", "transitive": 0, "version": 1}
```

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
