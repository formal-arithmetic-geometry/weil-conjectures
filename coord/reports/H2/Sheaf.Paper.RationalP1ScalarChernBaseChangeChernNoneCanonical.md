## What changed

Replaced the hole in
`AlgebraicGeometry.ProEtale.RationalP1.scalar_chern_base_change_chern_none_canonical`
with a reduction to the existing finite rational Chern exchange and coefficient
naturality. The theorem's signature is unchanged.

The proof constructs the two normalized completed lifts using the already proved
`diagonalTrace_completedChern_lift`, applies
`scalar_chern_base_change_chern_some_raw` at `bottomField l`, and removes the
finite unit and canonical pushforward isomorphisms. It then extends that equation
to the closure and unfolds the existing scalar Chern definitions. The finite
geometric calculation is shared with the finite coefficient branch instead of
being asserted again for closure coefficients.

Added `Sheaf.Paper.RationalP1ClosureExchangeNaturality`, containing the single
Chern-free statement `closure_exchange_naturality`. It concerns an arbitrary
adjunct, two rational/closure diagrams, and their existing scalar compatibility.
It contains no completed object, Chern class, normalization hypothesis, chosen
second adjunct, or Chern exchange hypothesis. Its finite base-changed adjunct is
an explicit composite, not a new datum or an assumed equation. The original
module has two new proof-only imports; its public imports are unchanged. No
existing definition, instance, public signature, or source-library file changes.
The item's DAG proof now records these actual dependencies.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.RationalP1.scalar_chern_base_change_chern_none_canonical`
(node `lem-sfb-rational-p1-scalar-chern-base-change-chern-none-canonical`).
The item has zero remaining holes. Added one hole:
`AlgebraicGeometry.ProEtale.RationalP1.closure_exchange_naturality`
(node `lem-sfb-rational-p1-closure-exchange-naturality`). Thus this is a decomposition:
one original hole closed and one simpler coefficient-naturality hole added, not
a net hole closure or a claim that the target is axiom-free.

Remote single-file compilation succeeded in import order: the new statement in
41.4 seconds and the item assembly in 50.1 seconds. Added the requested explanatory
comment for the item's local heartbeat budget. The delivery tool runs the final
compilation, interface, axiom and packet checks.

The finite theorem `scalar_chern_base_change_chern_some_raw` is an existing
statement with an existing hole, reused without changing its module or node.
The combining proof constructs both witnesses and performs the cancellation and
coefficient transport in Lean; no hole remains inside that proof. No hollow
definition or witness chosen from an undetermined existence theorem is added.

The new coefficient statement was checked mathematically for the bottom field,
the zero adjunct, and empty schemes. Zero maps stay zero. Empty schemes give the
unique maps. The coefficient and root maps remain the specified colimit legs at
the bottom field. The argument uses naturality and mates, not invertibility of
an exchange, proper base change, bounded continuity on unbounded objects, or a
basis of the Tate line. Its supplied endpoints and restriction squares are
uniquely pinned by their normalizations.

## No longer needed

The old direct proof dependency `lem-sfb-rational-p1-second-pretrace` is not used
to prove this Chern compatibility: it handles projection/inverse-map bookkeeping,
not Chern preservation. It is removed from this item's `proof_deps` and proof
steps. `Sheaf.Paper.RationalP1SecondPretrace` remains a transitive public import
of `RationalP1ScalarChernMaps` and remains used elsewhere; no library module is
withdrawn and no global pruning of that module is claimed. No pre-existing Lean
import is removed. The completed Chern lift and scalar Chern map dependencies
are retained. No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan says to perform the geometric exchange, but the
listed second-pretrace theorem does not state that a Chern class is preserved.
Its use alone cannot close the hole. The finite coefficient branch already has
an explicit statement of the geometric Chern calculation, so this closure branch
can reuse it. What is separately needed is coefficient/exchange naturality with
the exact unit, root-line, right-derived-model, and shift normalizations.

Mathlib searches found generic mate composition theorems, not this endpoint
identity. The project already proves generic coefficient exchange from a pull
cube and counit equations and proves finite-to-closure exchange on bounded
constructible categories. Those results are useful for the new lemma's proof;
they do not directly identify the arbitrary Diagram endpoints in its statement.
The new node and docstring give the normalization and mate-pasting argument.
Useful proved APIs for its implementation are the private generic
`derived_pull_comp` in `ContinuousIntegralPullComposition`, the private generic
`push_pull_counit` in `ContinuousIntegralExchangeTargetAdjunct`, and
`square_unique` in `DiagonalUniformizerMateComparison` (available by proof-only
`import all`). They respectively give native pull-composition coherence, the
counit equation for the push/pull coefficient mates, and uniqueness of the
full-unit-normalized derived restriction square. For the endpoint square,
`CartesianAdicComparison.qbar_coprojection` in `CartesianCoefficientTwists`
fixes the exact finite-to-closure root leg; `Endpoint.normalization` fixes the
derived scalar endpoint. These are routes for the remaining proof, not claims
that the new theorem is already proved.

The item's docstring carried its parent's blueprint id; it now carries its own
id. The existing ancestry metadata mixes module names in `created.item` with
node ids, so `blueprint_refs.py ancestor` returned a null ancestor. The new node
records the actual rational-triangle blueprint ancestor, following the existing
Chern-component and scalar-trace records. Existing ancestry records were not
edited.

## New nodes

`lem-sfb-rational-p1-closure-exchange-naturality`, attached to
`Sheaf.Paper.RationalP1ClosureExchangeNaturality`, isolates finite-to-closure
scalar naturality of base change on an arbitrary adjunct. Its proof normalizes
the supplied right-derived squares, takes mates of the coefficient pullback
cube, uses the normalized unit and Tate coprojection squares, and applies
naturality to the adjunct. Its source is diagonal-tower coefficients (2)-(3),
used in the second rational P1 triangle. It is strictly a coefficient-transport
step: the geometric Chern identity remains supplied by the existing finite
coefficient theorem. Generic off-unit tools for this step are
`lem-weil-pbc-coefficient-exchange-mates` (mate calculus),
`def-weil-pbc-ambient-ringed-exchange` (the specified native exchange), and
`det-prop-sfb-cartesian-coefficients-twists` (the prescribed root pullback and
coprojection square). These preserve the rational P1 unit route. No change
record is needed because no existing interface outside the item changes.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ClosureExchangeNaturality": "67ccf54e0ea103e311e22eabf5430fc9eae9dfce", "Sheaf.Paper.RationalP1ScalarChernBaseChangeChernNoneCanonical": "a8e972e17896e59d7dc4f4d159e12e1a77d1a99e"}, "results": {"Sheaf.Paper.RationalP1ScalarChernBaseChangeChernNone": {"hash": "9ffe1f004aa401e3aa9d5a1c5f6b6d65addd9e51", "status": "OK"}}, "seconds": 239, "time": "2026-10-28T10:39:53+0800", "transitive": 0, "version": 1}
```

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
