## What changed

`Sheaf.Paper.LocallyFiniteAdicFunctorDescentHom` now proves
`WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_descent_hom`
with its original signature. Its injectivity argument represents both arrows at one
finite field, cancels the tensor comparisons and uses the already proved split-coefficient
derived faithfulness theorem. Its surjectivity argument uses the existing condensed
filtered two-colimit's `homSurj`, then fullness of finite realization and the representative
formula. The proof does not assume the desired common-stage Hom bijection.

The new module `Sheaf.Paper.LocallyFiniteAdicCondensedStageComparison` constructs the
actual native-to-condensed ring map, restriction equivalence and its derived equivalence.
All those definitions and instances are proved, with no arbitrary choice of data from an
unproved existential theorem. `CondensedStageComparison` records full faithful finite
functors, their scalar natural isomorphisms, object comparisons and the explicit formula
on a finite-stage representative. Its existence is the one remaining named theorem.
It asks for no closure Hom descent or essential-image result. Essential surjectivity of
the finite functors is deliberately unnecessary.

The old item node's proof and proof dependencies follow these two explicit arguments.
One new node records the finite tensor normalization step. No existing statement,
definition, attribute or public import was changed; no other existing module was edited.

## Proved and sorry left

One original hole closed:
`WeilConjectures.LocallyFiniteAdicRealization.normalizedFunctor_descent_hom`
(node `lem-sf-locally-finite-adic-functor-descent-hom`). No sorry remains in the item.
The private helper `finiteCondensed_faithful` is also proved.

One hole added and left:
`WeilConjectures.LocallyFiniteAdicRealization.condensedStageComparison_exists`
(node `lem-sf-locally-finite-adic-condensed-stage-comparison`). Its docstring gives the
complete proposed construction from integral identity, rational realization, section-module
encoding, tensor normalization and localization naturality.

This is a decomposition: one upper hole closed and one strictly smaller coefficient
comparison hole added, net zero. The remaining theorem has no common-stage Hom bijection
as a hypothesis or conclusion. The real combining proof supplies both Hom-surjectivity
and Hom-injectivity, using the previously existing condensed two-colimit and split-unit
faithfulness results. The coefficient map, module equivalence and derived equivalence in
the new module have no holes. Final single-file server checks passed: the comparison
module in 16.9 seconds, and the item in 12.7 seconds. The original theorem signature
was checked unchanged, both files meet the 100-character line limit, all newly listed
direct node dependencies exist, and the new node creates no dependency cycle through
either changed node. The delivery tool performs the independent preflight and consumer
checks before pushing.

## No longer needed

Removed the item's direct proof imports:

- `Sheaf.Paper.ContinuousRationalDerivedRealization`: finite realization is now an
  ingredient of the finite tensor comparison node, not an unused import of the Hom proof.
- `Sheaf.Paper.RationalCoefficientCategoryComparison`: its global comparison, Frobenius
  and scheme-coherence package are unnecessary. The new comparison plan uses the smaller
  existing `FdIntegralIdentityRationalEquivalence` and `FdCompletionInverseScalarCoherence`
  finite declarations instead.
- `Sheaf.Paper.CondensedFlatCoefficientCalculus`: the Hom proof invokes
  existing derived coefficient faithfulness directly. It needs no separate flat coefficient
  calculation here; tensor normalization uses the existing internal/section scalar API.
- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` and
  `Sheaf.Paper.CondensedQbarLfpLocalTriviality`: no essential-image argument
  or conversion of arbitrary locally finitely presented modules to locally free modules
  is needed for this Hom theorem. The finite comparison only preserves locally free
  constructibility, and does not assert an essentially surjective finite functor.
- `Sheaf.Paper.CondensedQbarFunctionCoefficients`: not directly used in the
  Hom proof. The new coefficient comparison uses its coefficient identification together
  with `CondensedQbarCoefficientConstruction`; it is not claimed globally pruned.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`: no redundant
  direct import; it is public in the new comparison module because the comparison's
  statement uses its finite categories, transition functors and tensor associators.

The original direct proof dependency
`lem-fd-rational-coefficient-category-comparison` is replaced by its smaller finite inputs.
`lem-per-continuous-rational-derived-realization` remains needed below the new comparison.
`prop-weil-pbc-qbar-condensed-two-colimit` remains needed for Hom-surjectivity; its eventual
injectivity and object-surjectivity clauses are unused. No whole existing module is
withdrawn, and no global pruning claim is made for modules still imported elsewhere.
No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan's finite comparisons do not literally target the existing condensed
category: the raw rational stages, sectionwise continuous modules and internal modules
have different coefficient presentations. Importing the two broad realization theorems
does not by itself supply the native-normalized representative equation. The new node
states precisely that missing coefficient and tensor comparison, without restating Hom
descent. The source's finite realization and common-field descent are distinct steps.

The DAG's suggested eventual-injectivity step is unnecessary because the existing
`faithful_leftDerivedExtendScalarsToPadicAlgCl` theorem proves faithfulness at each finite
field. The proof uses that stronger already proved tool and cancels the finite maps.

Read Bhatt--Scholze Lemma 6.8.2, Proposition 6.8.11(3), Proposition 6.8.14 and Remark
6.8.15 in the local PDF. Edge cases checked in the new statement: equal fields and unit
comparisons, zero objects and arrows, empty schemes, arbitrary ramification, no chosen
finite-field base of X, and general scheme universe. Only finite-field preservation of
local freeness is used, not a converse for arbitrary modules.

Tool-node use outside the inherited unit: the finite integral/rational comparison,
continuous coefficient encoding and internal/section scalar adjunction supply coefficient
normalization; the condensed two-colimit and split derived faithfulness supply the actual
Hom descent. These do not replace a biduality step. The unit record has no realized nodes
for this item, and `blueprint_refs.py ancestor` returns None for its inherited chain. The
new node retains that fact, citing the current final paragraph of
`cor-coef-verdier-weil-equivariance.proof.md` and its common finite-field passage.
No maintainer tool approvals were added or rewritten.

## New nodes

`lem-sf-locally-finite-adic-condensed-stage-comparison`, in
`dag/nodes/sec-six-functors/lem-sf-locally-finite-adic-condensed-stage-comparison.json`,
realized by `Sheaf.Paper.LocallyFiniteAdicCondensedStageComparison`. It isolates finite
coefficient realization and its explicit native tensor normalization. The statement
includes the scalar and representative equations, and the proof names the existing finite
identity, continuous realization, scalar and section-module comparison declarations.
Three kinds of Mathlib search were actually run and recorded: LeanSearch, LeanFinder
and grep (plus Loogle for the generic full-faithfulness API). No exact existing finite
normalized comparison was found. Blueprint searches for finite coefficient realization
and condensed stage found no duplicate imported node. There are no change records because
only the item, its node, and this new module and node are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LocallyFiniteAdicCondensedStageComparison": "9acc1cbe9b1eb68258ff50a71a7342492e8e8ea6", "Sheaf.Paper.LocallyFiniteAdicFunctorDescentHom": "e8e156c1f20b1c6e526da58674687dde7dc723bb"}, "results": {"Sheaf.Paper.LocallyFiniteAdicFunctorDescent": {"hash": "5faeced6a7cc469b2c116417093b5ee54ffe2443", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T10:29:13+0800", "transitive": 0, "version": 1}
```

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
