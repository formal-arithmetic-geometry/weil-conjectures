## What changed

Proved `AlgebraicGeometry.ProEtale.integralTensorConstructibility` with its signature and
existing docstring unchanged. Added proved private helpers for the integer-ring isomorphism, its constructibility
comparison, and exact scalar restriction. The isomorphism and one-way comparison are
the proved constructions previously used in IntegralContinuousEncodingConstructible;
keeping them private here avoids importing that much larger section-encoding module. Private proof imports expose
the existing small coefficient isomorphism, integral local-model comparison and scalar
transport, the spectral/absolute-value topology equality, tensor closure, and derived
monoidal-equivalence comparison. Public imports are unchanged.
The DAG now records this shorter route through the already proved local finite-resolution
and finite truncation tensor calculation.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.ProEtale.integralTensorConstructibility`
(node `lem-sfb-integral-tensor-constructibility`). No new holes; zero `sorry` declarations
remain in the item. The private helpers are proved; the isomorphism is an explicit construction. No arbitrary
existence witness is introduced. This is a proof from existing library
declarations, not a decomposition. The final single-file compile passed without warnings in 25.5 seconds.
Delivery checks and the axiom probe are recorded by the delivery tool.

## No longer needed

No existing imports were removed; all three existing public imports support the statement.
The proof no longer directly needs these original planned dependencies:

- `sk-lem-int-integral-heart` / `Sheaf.Paper.IntegralConstructibleHeart`;
- the preservation and generation declarations of `det-lem-int-tensor-shriek` (its module
  remains a proof import solely for the proved small-coefficient isomorphism helper);
- `det-lem-int-tensor-projection` / `Sheaf.SixFunctors.IntTensorProjection`;
- `det-lem-int-tensor-pullback` / `Sheaf.Paper.IntegralTensorPullback`;
- `sk-lem-integral-models` / `Sheaf.Paper.IntegralModels`;
- `lem-sfb-finite-free-dual-chain-comparison` / `Sheaf.Paper.FiniteFreeDualChainComparison`;
- `lem-zl-condensed-lisse-proetale-locality` /
  `Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality`;
- `lem-sfb-dualizable-integral-completion` /
  `Sheaf.SixFunctors.DualizableIntegralCompletion`;
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` /
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`;
- `lem-sfb-field-bounded-constructible-tensor` /
  `Sheaf.Paper.FieldBoundedConstructibleTensor`;
- `sk-thm-pe-constructible-comparison` /
  `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`.

These are removals from this node's direct proof route, not module withdrawals or claims
that their other library consumers have vanished. No module is deleted.
The existing closure theorem replaces completeness, residue reduction and etale-origin
glue by the proved local finite-resolution calculation and two finite truncation inductions.

## Where the brief, the DAG or earlier work was wrong

The original DAG route is valid but unnecessary for the constructibility clause alone:
`boundedConstructible_tensor_closure` already proves the needed closure after comparing
coefficient presentations and constructibility predicates. Its small-field restriction
requires actual coefficient transport; it cannot simply be applied to arbitrary-universe E.
The unit's `realized` lists are empty. No unit statement, target, definition, public
signature or source-library declaration is changed. Empty schemes, zero modules and
rank-zero models are handled by the existing equivalences and tensor theorem.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
