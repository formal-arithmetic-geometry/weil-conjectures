## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeQuasiSeparatedAffineChartPointFibres`
states `AlgebraicGeometry.AlgebraicSpace.relative_qs_affine_chart_point_fibres`.
Its only theorem has proof `by sorry`; there are no new definitions, dependency
repairs, or statement corrections. The node changes only in `lean`.

Hypothesis and conclusion correspondence:

| Node text | Lean rendering |
| --- | --- |
| S is an arbitrary scheme | `{S : Scheme.{u}}` |
| X is an algebraic space over S | `(X : AlgebraicSpace S)` |
| Field-valued point classes and atlas topology | `Point X.obj.obj` and the imported `pointTopologicalSpace` instance |
| Representable relative diagonal quasi-compact on scheme tests | `hdiag : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))` |
| W is a scheme over S | `W : Over S`; its structure map is `W.hom` |
| W is affine, isomorphic to Spec A | `[IsAffine W.left]`, Mathlib's canonical spectrum-isomorphism criterion |
| a is a representable étale map to X | `a : yoneda.obj W ⟶ X.obj.obj`, `ha : IsEtale a` |
| W → S factors through an affine open | `hbase : ∃ V : S.Opens, IsAffineOpen V ∧ ∃ b : W.left ⟶ V.toScheme, b ≫ V.ι = W.hom` |
| Put R = W ×_X W, with projections s,t | `R : Over S`, `s t : R ⟶ W`, and `hR : IsPullback (yoneda.map s) (yoneda.map t) a a` |
| Every x in the point set | `∀ x : Point X.obj.obj` |
| Finitely many chart points over x | `Set.Finite {w : W.left \| schemePointMap a w = x}` |
| Finitely many relation points over x | `Set.Finite {r : R.left \| schemePointMap (yoneda.map s ≫ a) r = x}` |

The product in the presheaf category on `Over S` is the relative product over S.
Consequently the displayed diagonal is Δ_(X/S), not an absolute diagonal. Mathlib's
`QuasiCompact` says precisely that inverse images of compact open subsets are compact.
`IsRepresentableWith` supplies a representing scheme pullback with that property for
every scheme test. No topological quasi-compactness assumption on an arbitrary
field representative is introduced.

The `hR` square specifies the relation object; it is not an additional geometric
condition on a chart. Such a representation exists because a is representable étale.
The theorem is independent of the chosen representing scheme: every Yoneda pullback
square is uniquely isomorphic to the sheaf fibre product, preserving s and t.
The point map of a ∘ s is written directly as `schemePointMap (yoneda.map s ≫ a)`.
This avoids defining another point map or another fibre-product construction.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, and `Spec.map` (the spectrum is used through the affine criterion and
  point-representative interface, with `Scheme.isoSpec` in `AffineScheme`).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and `AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `AlgebraicSpace.Point`
  and `AlgebraicSpace.schemePointMap`, exposed by the topology module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicSpace.pointTopologicalSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used
  by the existing representable-étale predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` and
  `AlgebraicSpace.etale_fibreProduct_isScheme`. These supply the sheaf-product
  semantics; its representing square uses `CategoryTheory.IsPullback` from
  the already imported Mathlib pullback interface.

All available proof-dependency modules are imported with plain `import` when they
are not also statement dependencies: the point-open calculus module, the upstream
étale-fibre theorem, Mathlib Pullbacks (affine spectrum products), QuasiSeparated
(affine qcqs and qcqs permanence), and Limits.MorphismProperty (finite limits on
the étale categories). The statement-dependency modules use `public import`.
The theorem docstring reproduces all five proof steps and names their DAG inputs.

Edge cases checked before writing and on rereading:

- Empty W is affine (the zero-ring spectrum); no inhabitedness assumption occurs.
  Its represented self-relation is empty, and both sets are empty.
- If x is outside the image of the chart, the chart fibre is empty and so is the
  relation fibre, because its map factors through W.
- Empty X makes the universal conclusion vacuous. Empty S presents no difficulty.
- A chart that is not surjective and a structure map W → S that is not surjective
  are both admitted. There is no `IsSurjective` or `Surjective` hypothesis.
- S need not be quasi-separated or affine; the supplied affine base open is exactly
  the node's local factorization, and hdiag is relative over the original S.
- No finite-type, finite-presentation, or Noetherian assumption is added; étaleness
  is the existing predicate. The single universe u matches the existing algebraic
  space and test-scheme interface, and points have universe u+1 as recorded.
- R is not assumed affine, quasi-compact, or surjective over W as an extra input.

Searches (2026-10-24; wrapper logs in the sandbox `searches.jsonl`):

- LeanFinder: “For an algebraic space with quasi compact relative diagonal, an affine
  etale chart and its relation have finite point fibres”. Eight hits, including
  scheme finite-fibre theorems and affine-diagonal properties; no matching statement.
- Loogle: `AlgebraicGeometry.AlgebraicSpace, AlgebraicGeometry.QuasiCompact`.
  Zero hits; the service does not know the project's AlgebraicSpace declaration.
- LeanSearch: “An affine etale chart of an algebraic space with quasi compact relative
  diagonal has finite point fibres”. Eight hits, including `LocallyQuasiFinite`,
  `IsFinite.finite_preimage_singleton`, and scheme diagonal criteria. None concerns
  algebraic-space point classes and the chart relation.
- Wrapper grep in Mathlib/AlgebraicGeometry:
  `AlgebraicSpace.*[Ff]inite|[Ff]inite.*schemePointMap|IsRepresentableWith.*QuasiCompact`.
  Zero hits.
- `rg` in `lean/WeilConjectures` for `AlgebraicSpace|schemePointMap`, and for the
  exact node id: no hits. The broad finite-fibre search found only scheme results.
- `rg` in `lean/Sheaf` for point-fibre finiteness, relative diagonals, and the
  proposed declaration name: existing point definitions and scheme-test predicates,
  but no theorem matching both conclusions. In particular
  `AlgebraicSpaceDenseSchemeOpen` uses the same `IsRepresentableWith` diagonal test;
  `AlgebraicSpaceAbsoluteQuasiSeparated` is a different absolute notion, and
  `ProperCurveModuli.MapIsQuasiCompact` tests compactness of point spaces over affine
  schemes. The statement uses the node's explicit scheme quasi-compactness criterion.

Source checked in local Stacks sources: `decent-spaces.tex`,
`lemma-UR-finite-above-x` (03JV), condition (1) and the field-pullback argument;
`lemma-bounded-fibres` (03JX); and `spaces-properties.tex`,
`lemma-quasi-separated-quasi-compact-pieces` (03W7), including the relative affine
product diagonal test. No node fault or mathematical dispute was found.

Validation: prescribed `scompile.py` succeeded in both sandbox mode (5.5 seconds)
and the actual library module path (5.4 seconds), with no diagnostics.

## Second reading by Q30

I reread the node and completed file together as a separate pass. This is a worker
self-check; the dispatcher brief assigns the independent review to the maintainer
and explicitly prohibits starting other agents.

I checked that hdiag uses the presheaf product over S, that the base factorization
uses an actual affine open and its inclusion, and that ha includes representability.
The square hR is the universal sheaf pullback square, not merely an equality of
composites; thus it specifies R = W ×_X W and both projections. The two `Set.Finite`
clauses concern ordinary scheme points mapping to exactly the same class x, and
the second map is a ∘ s. The first clause is not a geometric-fibre cardinality
assertion. No nonempty or surjectivity hypothesis has appeared. The proof docstring
includes the quasi-compact affine product argument, both discrete finite point
sets P and Q, and the projection-compatible triple identification. No mismatch
was found and no statement changes were needed.
