## What changed

Replaced the hole in `WeilConjectures.IntegralHom.comparison_representative_square`
without changing its signature or public imports. Private proved helpers construct
the scalar internal-Hom isomorphism directly from the supplied presentations,
prove its naturality and its formula on the specified comparison, prove that
`I tensor Q` is K-injective at the independent universes of the item, and prove
invertibility of `homModelMap` on a K-injective target. The target endpoint is
then constructed explicitly and the square follows by uncurrying and cancelling
that endpoint isomorphism.

Added `Sheaf.Paper.IntegralHomReducedEvaluation` for the remaining completed-ring
chain evaluation calculation. Its statement allows any K-flat coefficient
resolution; it contains no finite-coefficient internal Hom, no normalized
comparison map, and no K-injectivity assertion for `I tensor Q`. The new statement
is the source-representative/evaluation part of the argument, whereas the item
now proves the scalar-Hom change of coefficients, the finite-free K-injectivity
argument, the target-representative identification, and the final square.

The new lemma is tested conceptually on zero complexes, the empty site, index
zero (the level-one quotient), and arbitrary augmentation identifications. None
requires a nonzero ring, a nonzero complex, or a canonical choice of augmentation.
The same augmentation occurs on both sides of its equality. Its docstring gives
the construction through K-flat resolutions, ordinary scalar tensor comparison,
and the evaluation and normalization fields of the supplied presentations.

## Proved and sorry left

Closed the original body of
`WeilConjectures.IntegralHom.comparison_representative_square` (one original hole).
All six private auxiliary declarations are proved: `homModelMap_isIso`,
`twoTerm_tensor_isKInjective`, `scalarHomBijection_precomp`, `scalarHomIso`,
`scalarHomIso_rep`, and `scalarHomIso_comparison`. The private definition
`scalarHomBijection` is an explicit composition of equivalences and contains no
hole or arbitrary existence choice.

Added one hole:
`WeilConjectures.IntegralHom.reduced_evaluation_representative`, node
`lem-sf-integral-hom-reduced-evaluation-representative`, in its own new module.
There are zero holes left in the item module, one in the delivery. This is a
one-for-one decomposition, not a proof with zero remaining obligations or a net
hole reduction. The remaining statement does not assert the original square
under a different name: the scalar-Hom target and finite-free argument are
absent from it and are proved in the item.

## No longer needed

No original import was removed; the original sole public import is retained.
The item no longer needs the separately chosen scalar-Hom models of
`lem-sfb-dc-hom-scalar-adjunction` / `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`.
Its arbitrary supplied tensor presentations are handled by the five natural Hom
bijections instead. It also does not import
`lem-weil-pbc-split-perfect-tensor-kinjective` /
`Sheaf.Algebra.Homology.SplitPerfectTensorKInjective`: that theorem fixes the site
and coefficient universes equal. Its dual-complex proof is specialized privately
to the two rank-one terms with independent universes. These are removed from the
item's proof dependencies. No whole-library pruning is claimed: other nodes can
still require those modules. K-flat resolution and derived scalar adjunction
remain required. The component-isomorphism result for the signed map is not used
to prove this normalization square; its import remains because it supplies the
statement's signed-map vocabulary.

## Where the brief, the DAG or earlier work was wrong

The scalar internal-Hom existence theorem in the original plan chooses its own
monoidal models, rather than furnishing an isomorphism for the arbitrary
`TensorPresentation` and `ReductionPresentation` supplied to this theorem.
Direct use would require an extra transport argument. The proof instead constructs
that isomorphism from the supplied adjunctions and `mu`, proving both inverse
identities by naturality. The planned split-perfect K-injective theorem also has
equal universes, unlike this item; the private bounded-dual proof avoids changing
its existing statement. No mathematical statement has been weakened or disputed.
The blueprint unit's route and the item signature are preserved.

## New nodes

`lem-sf-integral-hom-reduced-evaluation-representative` records the completed-ring
source-representative/evaluation subargument of paragraphs 1--2 of
`lem-coef-integral-hom-reduction.proof.md`. It has its own public theorem, complete
proof in words, three actual Mathlib searches, declared dependencies and Lean
attachment. It drops all two-term restrictions and does not claim the finite-ring
Hom endpoint or the final normalization square. No existing module besides the
item is changed, so there is no change record or forced adaptation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomReducedEvaluation": "18c7657383879e9135d3da17ad0fce3627bc228d", "Sheaf.Paper.IntegralHomRepresentativeSquare": "7457790233419ee3b3ed8326f13e84836f872b38"}, "results": {"Sheaf.Paper.IntegralHomComparisonRepresentative": {"hash": "8363f1d3880d9b4b715f4a2352048b16cf8885ba", "status": "OK"}}, "seconds": 38, "time": "2026-10-28T10:37:09+0800", "transitive": 0, "version": 1}
```

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
