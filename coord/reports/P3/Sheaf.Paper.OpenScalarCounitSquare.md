## What changed

Proved the open-unit, scalar-counit square and identity-normalization theorems in
`Sheaf.Paper.OpenScalarCounitSquare`, preserving every existing public signature,
definition and public import. Added proved private lemmas for the exact-localization
unit and Hom formulas, preservation of left-adjoint uniqueness, the tensor comparison's
unit equation, and the counit and identity calculations.

Reduced `openScalarCounitRestriction` to one new theorem,
`AlgebraicGeometry.ProEtale.openScalarRestrictionUnit`, in
`Sheaf.Paper.OpenScalarRestrictionUnit`. Its tensor half is proved by composite adjoint
uniqueness and coordinate transport. The remaining theorem is only the scalar
restriction unit equation, not the conjunction or the scalar counit square.

The complete sandbox compiles in import order: the new module in 4.0 seconds and the
item in 12.9 seconds, without errors or warnings. Existing definitions were not changed;
no other existing Lean module or node was adapted. The unit's blueprint route is kept.

## Proved and sorry left

Original holes: four. Closed all four bodies in the item:

- `AlgebraicGeometry.ProEtale.openScalarCounitUnit`: proved from exact localization,
  fully faithful intrinsic open extension, and unit-preserving adjoint uniqueness.
- `AlgebraicGeometry.ProEtale.openScalarCounitSquare`: proved from the two restriction
  unit equations and Mathlib's `mateEquiv_counit_symm`, by an explicit Hom calculation.
- `AlgebraicGeometry.ProEtale.openScalarCounitIdentity`: proved from the square, the
  published scalar restriction identity, and the scalar adjoint-uniqueness counit formula.
- `AlgebraicGeometry.ProEtale.openScalarCounitRestriction`: decomposed; its tensor
  equation is proved, and its scalar restriction equation is the new smaller theorem.

Added one hole, the only sorry left in the delivered Lean files:
`AlgebraicGeometry.ProEtale.openScalarRestrictionUnit`
(node `lem-sp-open-scalar-restriction-unit`). This is the original restriction theorem's
first conjunct. Its docstring and node give the ordinary sheaf normalization,
constant-pullback coordinate compatibility, exact localization, and unit transport proof.

Thus three original holes are proved and one is decomposed, with one lower hole added:
net three fewer holes in this packet. The square and identity theorem still depend on
that named lower theorem; this is not a claim that their axiom closures are sorry-free.

## No longer needed

Removed the three proof imports:

- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.SixFunctors.OpenScalarTensorNormalization`
- `Sheaf.SixFunctors.KFlatScalarComparisonNormalization`

Removed their nodes from this item's proof dependencies and obsolete top-level tool
approvals: `lem-sf-open-tensor-normalization`,
`lem-fix-open-scalar-tensor-normalization`, and
`lem-sfb-kflat-scalar-comparison-normalization`.
The first is replaced by the existing fully faithful extension instances and exact unit
localization calculation. The second is replaced by the unit equation of adjoint
uniqueness and coordinate naturality. The third is unnecessary because the specified
inverse tensor/pullback comparison is definitionally the scalar mate used in Mathlib's
counit equation. These are removals from this proof route; no claim is made that other
library users no longer need those modules. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The DAG's normalization interfaces were larger than this
proof needs. In particular one need not choose a monoidal model or invoke its existence
theorem to prove the prescribed scalar counit square or identity case. The direct mate
formula and left-adjoint uniqueness suffice. The remaining scalar restriction task is
the precise compatibility between the published sheaf normalization and the specified
constant-pullback coordinates; the tensor equation is independent of that task.

The current server queue assigned a proof route. Its older build-error record named
`Sheaf.SixFunctors.OpenScalarTensorNormalization`; this proof no longer imports it.
The original item and all public signatures remain present.

## New nodes

`lem-sp-open-scalar-restriction-unit`, realized by
`Sheaf.Paper.OpenScalarRestrictionUnit` and
`AlgebraicGeometry.ProEtale.openScalarRestrictionUnit`, extracts only the scalar
restriction unit half of the original Step 2. It is true on the empty open, the whole
open, zero complexes and nonflat finite coefficient maps: the argument concerns exact
restriction and preserves underlying sections, not derived flatness. The ordinary
normalization is already stated and proved in `sfOpenRestriction_normalized_unique`;
the remaining work is its prescribed coordinate change and exact localization.
LeanSearch, Loogle, LeanFinder and Mathlib grep results are in `searches.jsonl` and the
node. A whole-blueprint search for "scalar restriction unit" found no duplicate; the
nearest blueprint ancestor is `det-sp-tower-gluing`, Levels paragraph.
No change record is required, since no existing signature, definition or public import
was changed, and no other existing module was adapted.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.OpenScalarCounitSquare": "8c39a2ab1f4f6e3602494625dde5a48dcd5ad099", "Sheaf.Paper.OpenScalarRestrictionUnit": "05885da2edc255ffa4c6c22f729cfed6646a9498"}, "results": {"Sheaf.Paper.PfReductionProperOpenIdentities": {"hash": "a85a462ce772e7b315a19be49c8f462cc3c43c0b", "status": "OK"}, "Sheaf.Paper.RecordedOpenScalarNormalization": {"hash": "6ddad06def58cc249379fe7191d9426ad2f0d924", "status": "OK"}}, "seconds": 87, "time": "2026-10-28T03:33:33+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
