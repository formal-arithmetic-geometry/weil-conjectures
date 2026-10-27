## What changed

Corrected and proved
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.scalar_finite_squares`.
Its earlier split omitted the hypothesis `CompletedFormula l E L ι g b`; the
quotient square cannot hold for an arbitrary completed isomorphism. The only
caller, `scalar_finite_model`, already has this hypothesis. Its sole adapted line
passes `hb` to the corrected theorem, preserving its full public signature and
all target statements.

The quotient proof applies the existing completed tensor extensionality lemma,
the completed normalization, the two quotient formulas and the finite formula
with middle scalar one. The projection compatibility for the completed inverse
coefficient map finishes the calculation.

For transitions, the forward finite formula with middle scalar one determines
the inverse on finite pure tensors. Precompose by this inverse and use tensor
extensionality in the finite right model. Two proved private helpers justify this
extensionality: inverse image commutes with sheafification under the site
equivalence, and additive tensor induction checks the resulting presheaf maps.
The transition formulas then reduce to naturality of the finite coefficient
comparisons. No surjectivity, flatness, boundedness or new existence theorem is
used. Positive level one (`n = 0`), zero complexes and empty sites use precisely
the same identities.

Proof imports expose existing private tools from
`FiniteFreeCompletedScalarComparison`, `InverseImagePullbackComparison` and
`IsoSectionwiseInverseImage`. All public imports remain unchanged. The existing
transparency override is strengthened to respect transparency; large completed
coefficient constructions are locally irreducible. There is no changed shared
definition, instance or attribute.

The item's DAG node now records the corrected signature, the actual tensor
uniqueness argument and its dependencies. Change record:
`coord/changes/scalar-finite-squares-normalization.md`.

Validation: the item and its adapted caller compiled in import order against the
server library, in 28.1 seconds and 5.6 seconds respectively.

## Proved and sorry left

One original hole belonged to
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.scalar_finite_squares`.
Its corrected, source-faithful statement is fully proved; the original false
statement is explicitly repaired rather than claimed as proved unchanged.
The two new private helpers `inverseSheafify_ext` and `finiteRight_ext` are
proved. Neither delivered module contains any `sorry`. Holes added: zero;
split-off statements: zero. The parent's existing complete proof stays complete.
Inherited unproved dependencies, such as `scalar_finite_core`, are unchanged.

## No longer needed

The planned dependency
`lem-weil-isomorphism-scalar-quotient-chain-squares`
(`Sheaf.Paper.IsomorphismScalarQuotientChainSquares`) is not needed for this
uniqueness argument: it constructs comparisons, whereas this theorem already
receives comparisons and all finite formulas. Its proof-dependency edge is
removed from the item's node. That module may remain needed by other items,
including the finite core construction, so this delivery does not withdraw it.
No existing public import is removed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (original statement, repaired here): the five original
hypotheses never mentioned `b`, but the quotient conclusion did. For identity
pullback, equal fields over an odd prime and a free rank-one complex in degree
zero, both a normalized completed comparison and its negative are natural
isomorphisms. Replacing the former by the latter preserves every old hypothesis
and changes the sign of its nonzero finite quotient. Thus the claimed quotient
square cannot hold for both. The missing assumption is already required by the
source's normalized completed comparison and by the unchanged parent theorem.
The item node's `statement_change` records the sole citer and its compatibility.

The node's plan cited a construction theorem that produces its own finite maps;
that existential conclusion does not directly establish the squares for the
maps supplied here. The direct tensor uniqueness proof closes this gap without
another decomposition. The unit's statement and prescribed route stay intact.

The current server queue assigned ordinary proof work (one hole), with no
build-error or rework record for this item. The parent was unclaimed when its
one-line proof adaptation was prepared. No source-library file changes.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarFiniteModel": "3ae0a743ea9ba6265a29e448119fc038e09f3e2e", "Sheaf.Paper.IsomorphismScalarFiniteSquares": "9cb8a773a70ee46277d1936a79ca08373568b59e"}, "results": {"Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB": {"hash": "509334b55b7c9bc0b756950fac4c23d3b56a7f08", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarTensorKFlatModel": {"hash": "327a4898e867eaaef95b8967d5dc5396edb734cb", "status": "OK"}, "Sheaf.Paper.SfRecollementReductionBoundary": {"hash": "3e5eb049e528ed51a96a3b71024b90d9c96825a0", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityLineComparisons": {"hash": "7dfea4a2aa9ca58786b61db04994341c85d15175", "status": "OK"}}, "seconds": 139, "time": "2026-10-28T07:11:44+0800", "transitive": 4, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
