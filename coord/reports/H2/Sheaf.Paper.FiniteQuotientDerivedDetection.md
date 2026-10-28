## What changed

Filled `AlgebraicGeometry.ProEtale.DiagonalTrace.finiteQuotient_detects_derived_arrows`
in `Sheaf.Paper.FiniteQuotientDerivedDetection`, preserving its statement and all
hypotheses. The proof applies the existing degree-zero generator bijection,
acyclicity of forgotten injective finite module sheaves, and the existing abstract
Ext comparison. A proved private helper identifies that comparison with the actual
single/shift formula through Mathlib's `Ext.mapExactFunctor_hom`.

Validation: `lcompile.py` compiled the delivered module in 18.1 seconds.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

The mixed-universe Grothendieck theorem supplies enough injectives locally.
Updated the item's DAG proof, proof dependencies and proof origin to record this
composition of already available declarations. No other module or interface changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.DiagonalTrace.finiteQuotient_detects_derived_arrows`
(node `lem-sfb-finite-quotient-derived-detection`).

Holes added: zero. Holes left in the delivered module: zero. No new split statements.
The argument includes arbitrary module targets, the empty scheme, and the zero
coefficient ring: neither generator comparison nor the acyclicity argument imposes
a nonzero or nonempty assumption.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Paper.TowerClassFiniteUnit` (including its private declarations).
- `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients`.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective`.
- `WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`.
- `WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections`.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp`.
- `Mathlib.CategoryTheory.Sites.Equivalence`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.

The private regular-module normalization and universe-transport constructions are
already encapsulated by `finiteQuotient_hom_bijective` and
`finiteInjective_sections_acyclic`. Accordingly removed the direct proof-dependency
edges to `lem-sfb-tower-class-finite-unit` and
`lem-sc-injective-module-abelian-acyclic-zariski`. They remain dependencies of the
helper modules; no whole module or mathematical obligation is withdrawn. The
unit route remains intact.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The node's existing plan suffices
once its proved helper declarations are composed; another split is unnecessary.
The current queue row is a proof assignment with one hole, with no current rework
row or build-error file for this module in the shared snapshot.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientDerivedDetection": "e9589b96423626f59cd4e7909b715f615d990a50"}, "results": {"Sheaf.Paper.FiniteP1KummerBoundaryTransport": {"hash": "6a7202ac16388d895d7be714b9acb9bb71dea71f", "status": "SLOW"}}, "seconds": 299, "time": "2026-10-28T07:58:44+0800", "transitive": 0, "version": 1}
```

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
