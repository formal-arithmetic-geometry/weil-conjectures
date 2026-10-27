## Worker report

Item: lem-sfb-finite-chart-fibres-field-quasicompact. Group: Q02. Date: 2026-10-24.

The module `Sheaf.AlgebraicGeometry.FiniteChartFibresFieldQuasicompact` states
`AlgebraicGeometry.AlgebraicSpace.finite_chart_fibres_field_quasicompact` with proof
`sorry`. It adds no definitions, axioms, helper theorems or instances. Only the item's
`lean` field changes. There are no statement corrections or disputed assertions.

Source read: `literature/stacks-project/decent-spaces.tex`,
`lemma-UR-finite-above-x` (Tag 03JV), its six conditions and proof. Condition (2)
permits arbitrary schemes U_i; condition (6) concerns every field representative.
The declaration docstring carries all five proof steps from the DAG, including the
absolute-base reduction, the finite-fibre transfer, the residual-relation and
field-monomorphism steps, and the final finite-chart criterion.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the algebraic space is
  `(X : AlgebraicSpace S)`, using the recorded fppf-sheaf/representable-diagonal/atlas
  definition. Its point class is `(x : Point X.obj.obj)`.
- The set-indexed scheme family is `{I : Type w} (U : I → Over S)`; the maps
  `(a : ∀ i, yoneda.obj (U i) ⟶ X.obj.obj)` are S-morphisms of the represented
  presheaves. `w` is independent of `u`, allowing any set of charts.
- `(ha : ∀ i, IsEtale (a i))` is exactly representable étaleness, since this
  project's `IsEtale` includes scheme-test representability.
- `hcover : ∀ y : Point X.obj.obj, ∃ (i : I) (v : (U i).left),
  schemePointMap (a i) v = y` says precisely that the union of the images of
  the scheme point maps is the whole point set. No individual chart is assumed
  surjective or to meet x.
- `R : I → Over S`, its projections `p₁ p₂`, and
  `hR : ∀ i, IsPullback (yoneda.map (p₁ i)) (yoneda.map (p₂ i)) (a i) (a i)`
  specify the scheme representatives of U_i ×_X U_i and their two projections.
  This is the project's recorded representing-pullback interface, not an arbitrary
  scheme or map. Such squares exist by representability of the diagonal, and are
  unique up to unique isomorphism. Supplying a presentation imposes no extra
  mathematical restriction.
- `hU` is finiteness of `{v | schemePointMap (a i) v = x}` for every i, exactly
  the chart fibre. `hfinite` is finiteness of
  `{r | schemePointMap (yoneda.map (p₁ i) ≫ a i) r = x}`, exactly the relation
  fibre for the specified first projection.
- `∀ c : PointRepresentative X.obj.obj` quantifies over every field L in the
  site's universe, its S-structure and its map to X. The structure's fields are
  `K : Type u`, `[Field K]`, `base : Spec (.of K) ⟶ S`, and `value` in X at
  that field spectrum. The natural transformation for this section is the
  canonical `yonedaEquiv.symm c.value`. `Quot.mk _ c = x` says it represents x.
- `∀ (T : Over S), IsAffine T.left → ∀ t : yoneda.obj T ⟶ X.obj.obj` ranges
  over all affine tests. There is no `IsEtale t` assumption.
- The existential V, p, q and `IsPullback (yoneda.map p) (yoneda.map q) t
  (yonedaEquiv.symm c.value)` give exactly T ×_X Spec L as a scheme, with
  its canonical projections. `CompactSpace V.left` is its quasi-compactness,
  without a Hausdorff assumption. Uniqueness of representing pullbacks implies
  this condition for any representative of the fibre product.
- No quasi-separatedness, finite-type, Noetherian or compactness assumption on X
  or the U_i appears anywhere in the signature.

Recorded statement dependencies and declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme
  morphisms, `Spec`, `Spec.map` (spectrum is also present in PointRepresentative).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicGeometry.AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: the recorded point
  interface, through its public import of `AlgebraicSpacePointClasses`:
  `Point`, `PointRepresentative`, `schemePointMap`. The topology adds no
  hypotheses to this set-theoretic point criterion.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  used within the recorded representable `IsEtale` definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; the statement uses its representing-pullback
  formulation and `CategoryTheory.Limits.IsPullback` for scheme tests.
- `Mathlib.Algebra.Field.Defs`: `Field`, used by `PointRepresentative.field`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` on the representing scheme.

All dependency signatures and source docstrings were read. Stated proof dependencies
are plain imports: `SpaceChangeBase`, `ChartPairFiniteResidualRelation`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`,
`WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`,
`SpecFiniteProductFields`, and `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
The three proof nodes `lem-sfb-etale-chart-finite-fibre-transfer`,
`lem-sfb-finite-point-self-relation-field-monomorphism`, and
`lem-sfb-field-monomorphism-finite-chart-decency-criterion` currently have no Lean
record or Mathlib match and supply no import yet. They are proof inputs only;
none is needed to type this statement. No import cycle is introduced.

Edge cases checked: empty individual chart and relation fibres satisfy `Set.Finite`;
no nonemptiness is required of any of them. An empty index set cannot cover a space
with the specified point x, so the theorem is vacuous in that case, as it should be.
For an empty algebraic space there is no x. An empty affine test or empty fibre product
is permitted and is quasi-compact. Charts may be nonaffine and non-quasi-compact.
Fields have arbitrary characteristic and no finiteness assumption. All fields and test
schemes use universe u, matching the recorded big site; the index set has arbitrary w.
The use of an arbitrary base S, rather than Spec Z alone, matches the node and source.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Finite chart fibres and self relation fibres of an
  algebraic space imply every field representative is quasi compact"`: 8 hits,
  all scheme quasi-compactness/quasi-finiteness results (including `QuasiCompact`,
  `quasiCompact_of_compactSpace`, and quasi-compact scheme fibres), no algebraic-space
  pointwise chart/relation criterion.
- `msearch.py ... leansearch "Finite chart fibres and relation fibres imply every
  field representative of an algebraic space point is quasi compact"`: 8 hits,
  including finite and quasi-compact scheme fibres, `Algebra.QuasiFinite`, and
  affine-local quasi-compactness criteria; no matching statement.
- `msearch.py ... loogle '"AlgebraicSpace", "QuasiCompact"'`: 0 hits.
- `msearch.py ... grep 'AlgebraicSpace|finite.*chart.*fib' AlgebraicGeometry`:
  0 hits in Mathlib.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `finite_chart|finite.*relation.*fibre|field.*quasicompact|field.*quasiCompact`:
  only unrelated free finite affine-chart lemmas and scheme affine-cover material.
  Direct inspection found `DecentSpaceFiniteFieldMap`, whose hypothesis uses the same
  affine-test compactness encoding, but whose statement is a different finite-map result.
- `grep -rn 'lem-sfb-finite-chart-fibres-field-quasicompact' lean/WeilConjectures`:
  no matches. `rg` for the new declaration and module name across Mathlib,
  WeilConjectures, Sheaf and `dag/lean_names_upstream.json`: no matches.

Validation: the prescribed `scompile.py Q02 ...` compiled the module cleanly against
both its sandbox name and its delivered library module name (3.1 s and 2.2 s).
No non-sorry warnings or errors were printed. Every universe and variable is explicitly
bound, with `autoImplicit false`. Every Lean line is at most 100 characters.

## Second reading by Q02

This is the worker's own second reading; the dispatch brief assigns independent review
to the maintainer and prohibits starting other agents. No independent reader is claimed.
With the node and final Lean open, I rechecked the two different finite-fibre assumptions,
the orientation of both representing pullback squares, the first projection in the
relation-fibre condition, and the quantifiers over all point classes in hcover and all
representatives of x in the conclusion. They match. I also checked that the affine-test
map t has no étale hypothesis and that hU does not require nonempty fibres. No mismatch
or statement change was found. No new nodes or dependency modules are delivered.
