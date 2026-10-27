## Worker report

Module: `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreDimensionSupremum`.
The sole postponed theorem is
`AlgebraicGeometry.AlgebraicSpace.fibre_dimension_eq_supremum`.
Its proof is `sorry`; its docstring contains the five steps of the DAG proof.
The two helpers have real data: `residueFibrePresheaf` is a presheaf product and
`pointLiesOver` is the base-image predicate on existing field-valued point classes.
They construct the fibre and spell out the base-point condition needed for this node;
the repair adds a definition node binding the existing local relative fibre dimension,
without duplicating its Lean definition or repairing any landed dependency module.

Hypothesis and clause correspondence:

- The scheme `T` is `{T : Scheme.{u}}`; the algebraic space with its given morphism
  `f : X → T` is `(X : AlgebraicSpace T)`. This is the category of fppf sheaves over
  `T` with representable diagonal and an étale surjective scheme atlas. The structural
  morphism is retained in this over-base encoding, and `U.hom` is its composite with
  any scheme chart. This does not specialize the given morphism.
- The atlas topology is the imported `pointTopologicalSpace` on the already defined
  `Point X.obj.obj`. No topological Krull dimension of this point space is substituted
  for the chart dimension of the algebraic space.
- Local finite type on étale scheme charts is `hft`, universally quantifying over
  `U : Over T` and `a : yoneda.obj U ⟶ X.obj.obj` with `IsEtale a`, and requiring
  the recorded scheme property `LocallyOfFiniteType U.hom`.
- Quasi-compactness is `hqc`: for **each** scheme `V` over `T`, `CompactSpace V.left`
  implies the existence of a scheme `U` with `CompactSpace U.left` and a representable
  étale surjective map to `X ×_T V`. Both `IsEtale` and `IsSurjective` are exactly the
  existing scheme-test predicates. No affineness, separation, or finite-presentation
  condition is inserted in this hypothesis.
- The point `t ∈ T` is `(t : T)`. The fibre `X_t` is `residueFibrePresheaf X t`.
  The product with `yoneda.obj (Over.mk (T.fromSpecResidueField t))` is the fibre
  product over `h_T`, because `h_T` is terminal in presheaves on schemes over `T`.
  Thus it has exactly the compatible pairs of points/sections in the prescribed
  residue-field fibre, and is the same algebraic space viewed over its original base.
  A scheme map to this product includes its map to `Spec κ(t)` automatically.
- The condition `f(x) = t` is `pointLiesOver X t x`: there exists a field-valued
  representative `r` of `x` whose unique spectrum point maps to `t` under `r.base`.
  All representatives of a point have the same base image: their common-field
  restriction commutes with the base. The predicate therefore does not choose or
  alter a representative and imposes no residue-field rationality restriction.
- The existing `localFibreDimension X x` is exactly the node's `δ_f(x)`: the supremum
  over affine scheme charts and lifts `v`, of `topologicalKrullDimAt (U.hom.asFiber v)`.
  `asFiber` is the unique point above `v` in the scheme residue-field fibre.
  `topologicalKrullDimAt` is the infimum/minimum over open neighbourhoods, not the
  Krull dimension of a local ring. The existing definition is now owned by the new `def-sfb-space-local-fibre-dimension` node,
  recorded `existing: true` on the same landed declaration. Only this definition node
  is added to `stmt_deps`; the theorem node
  `lem-sfb-space-local-fibre-dimension-open` is not a statement dependency.
  The mathematical statement and Lean source are unchanged.
- Every occurrence of the displayed supremum over `U`, `IsAffine U.left`, `a` to
  `residueFibrePresheaf X t`, and `IsEtale a`, with summand
  `topologicalKrullDim U.left`, is exactly `n_f(t)` as defined in the node. It is
  written inline to avoid a second definition of algebraic-space dimension.
- The first conjunct is the equality of this supremum and
  `⨆ x, ⨆ (_ : pointLiesOver X t x), localFibreDimension X x`.
- The second conjunct is the exact equivalence between emptiness of the fibre's
  point classes and nonexistence of a point of `X` over `t`.
- The third conjunct states that both suprema are `⊥ = -∞` in the empty case.
- The last conjunct, for a nonempty fibre, gives `d : ℕ` and a point `x` over `t`
  with `δ_f(x) = d` and `n_f(t) = d`. Together with the first conjunct this says
  that `d` is the largest value of `δ_f` on that fibre. The empty/nonempty clauses
  also state exactly that the dimension lies in `{-∞,0,1,...}` and excludes `+∞`.
- There is no separatedness, properness, flatness, finite-presentation, Noetherian,
  nonempty-source, or nonempty-fibre hypothesis. The explicit universe `u` is the
  universe of the recorded algebraic-space framework; scheme charts and field-valued
  representatives use that same universe. No variable or universe is auto-bound.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsSurjective`, `IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  its public dependency `AlgebraicSpacePointClasses` supplies `Point`,
  `PointRepresentative`, and `schemePointMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  the recorded scheme quasi-compactness property is `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`. For this nonrepresentable source
  the node's scheme-atlas quasi-compactness is expanded as `hqc`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`, and the signature of `Scheme.Hom.residueFieldMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`, publicly imported for the fibre construction.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`;
  `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalFibreDimensionOpen`:
  `localFibreDimension`, used directly, and `localFibreDimension_chart_finite_isOpen`.
  Its node statement, record, full definition and theorem were read before use.
  The statement uses the plain definition, not the theorem; the new definition node
  supplies the binding required by the H2 return.
- Stated proof prerequisites are imported privately: `AlgebraicSpacePointOpenCalculus`
  (`point_open_calculus`), the upstream finite-type dimension module
  (`exists_topologicalKrullDim_le`), `DimensionSupremumLocalDimensions`
  (`topologicalKrullDim_eq_iSup_topologicalKrullDimAt`), and the Mathlib modules
  `Morphisms.QuasiSeparated`, `Morphisms.Etale`, and `Pullbacks` for affine QCQS,
  étale composition, affine fibre products and locally-finite-type base change.
  The scheme-fibre declaration `Scheme.Hom.fiber` is publicly available through the
  local-relative-dimension module. The two proof nodes without recorded statements
  (`lem-sfb-etale-topological-dimension-at-point` and
  `lem-trf-space-qc-finite-affine-atlas-refinement`) are identified in the proof
  docstring; they are not prerequisites to typing this statement.

Edge cases checked before writing: an empty source; an empty fibre over a nonempty
base; the empty scheme as a chart; dimension zero; fibres of positive and varying
finite dimensions; arbitrary residue fields and field extensions; a non-quasi-compact
base; and nonseparated finite-type sources. Empty charts contribute bottom, and empty
point-indexed suprema are bottom in `WithBot ℕ∞`. An empty `T` has no `t`, so the
pointwise theorem is vacuous without excluding that scheme. The bound and attainment
use quasi-compactness, and no artificial finite bound is supplied as a hypothesis.

Sources checked directly: `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-dimension-fibre` (Tag 0D4M), including its final scheme-target reduction;
`spaces-properties.tex`, `definition-dimension-at-point` and `definition-dimension`
(Tags 04N5 and 04N6). These explicitly distinguish algebraic-space chart dimension
from the topological dimension of the space of point classes. No statement fault or
statement correction was needed.

Searches, 2026-10-24:

- `msearch.py ... leanfinder "Dimension of a finite type algebraic space fibre equals
  the maximum of its local fibre dimensions on affine etale charts"`: eight results,
  about standard smooth relative dimension and finite/Jacobson scheme fibres; none
  states the requested algebraic-space dimension equality.
- `msearch.py ... loogle "topologicalKrullDim, Scheme.Hom.fiber"`: zero hits; the service
  also reported unknown identifier `Scheme.Hom.fiber` for the unqualified query.
- `msearch.py ... grep "fibreDimension|fiberDimension|relativeDimension"
  AlgebraicGeometry`: ten hits about scheme smooth relative dimension; no match.
- `msearch.py ... leansearch "algebraic space dimension fibre supremum local fibre
  dimension"`: eight results, including `topologicalKrullDim` and `Scheme.Hom.fiber`,
  plus unrelated Hausdorff-dimension and order-dimension statements; no full match.
- `rg -n "fibreDimension|fiberDimension|relativeDimension|<item id>"` in both
  `lean/WeilConjectures` and `lean/Sheaf`: unrelated rank/representation dimensions
  and scheme relative dimensions, not this theorem. Broader searches for
  `localFibreDimension` and algebraic-space dimension found the exact existing
  `localFibreDimension`, which is reused, and `etaleDimension`, whose local/global
  point-indexed definition differs from the raw affine-chart expression specified
  here. The latter definition is not duplicated.
- Exact proposed declaration-name searches across Mathlib, `lean/Sheaf`,
  `lean/WeilConjectures`, and `dag/lean_names_upstream.json` found no collision for
  `residueFibrePresheaf`, `pointLiesOver`, or `fibre_dimension_eq_supremum`.

Validation: `scompile.py Q46 lem-sfb-space-fibre-dimension-supremum <module>` passed
both sandbox and library-module compilation. All variables and universes are explicit,
all lines are at most 100 characters, and there is exactly one theorem with `sorry`.
The original dry run and the repair validation are distinguished below.

## Second reading by Q46

This is a separate second pass by the same worker: the dispatch brief forbids starting
other agents and reserves independent review to the maintainer. No independent worker
review is claimed here.

With the node and final module reopened, checked `hft` against every étale scheme chart
and `hqc` against every quasi-compact scheme test, rather than silently restricting to
affine tests. Checked that both uses of a presheaf product are over the terminal `h_T`:
the second coordinate is respectively the residue-field spectrum or the test scheme,
so these are the required fibre products, not unrelated absolute products of spaces.
Checked the base-point predicate on field representatives: `Quot.mk _ r = x` ties the
representative to the **same** point, and the image of its unique field-spectrum point
is exactly `t`, with arbitrary field extensions permitted. Checked that the local
summand uses the existing scheme-fibre lift and neighbourhood dimension, not a local
ring dimension. Matched the four conclusion conjuncts to equality, empty iff no base
point, both bottom in the empty case, and finite maximum in the nonempty case.
No missing hypothesis or altered clause was found. The only implementation adjustment
was to import the already landed local-relative-dimension owner and cite its node,
avoiding a duplicate Lean definition of `δ_f`. The return identified that citing its
theorem owner as a statement dependency was incorrect. The repair adds the definition
node below and cites it instead; no dependency modules are changed.

Original delivery validation (before return H2): `deliver2.py Q46 lem-sfb-space-fibre-dimension-supremum --no-push`
printed `OK (dry run): commit 2deb5d79c88 passes the preflight and compiles; nothing pushed`.
The final module compiled in both sandbox and library mode in 1.5 seconds each, with
no errors or unexpected warnings. The only node changes are `lean` and the single
statement-dependency addition then present. That addition was returned as H2 and is
replaced by the new definition node in this repair.


## New nodes

`def-sfb-space-local-fibre-dimension` owns the local relative fibre dimension
`δ_f(x)`, defined as the supremum of `topologicalKrullDimAt (U.hom.asFiber u)`
over affine representable étale charts and lifts of `x`. Its source is Stacks
04NM(3), `spaces-morphisms.tex`, `definition-dimension-fibre`, specialized to a
scheme target. The source definition and explanatory chart discussion were reopened.
The new node has no finite-type or quasi-compactness assumption, because construction
of the supremum needs neither. A point of a chart determines its image in `T`, its
scheme fibre over that image, and its unique lift by `Scheme.Hom.asFiber`.
The node cites the existing definitions of schemes, algebraic spaces, point classes,
scheme fibres, and neighbourhood dimension. The schema uses exactly those cited
nodes as `stmt_deps`, no proof dependencies, and `import_flags: []` because the item
is reached from the project targets.

This is an `existing: true` binding to
`AlgebraicGeometry.AlgebraicSpace.localFibreDimension` in the already landed
`Sheaf.AlgebraicGeometry.AlgebraicSpaceLocalFibreDimensionOpen`, line 48. Its
signature is copied verbatim and its body is an explicit `iSup` with real data.
The old theorem node lists the declaration as a helper, but is not a definition
node. Return H2 specifically requires this definition-node ownership instead of
citing that theorem as a statement dependency. No Lean definition is copied and
neither the existing module nor its landed theorem is edited.

Fresh searches are preserved verbatim in the new node's `mathlib_searches`:
LeanSearch for the local relative dimension defined on affine étale charts returned
eight scheme/smoothness results, with no match; LeanFinder for the same supremum
returned eight scheme/smoothness results, with no match; Mathlib grep for
`localFibreDimension|localFiberDimension|dimension.*[Ee]tale.*chart` returned no hits.
Repository/DAG grep found the existing real-data definition and its theorem-node
helper record, and no definition node for this notion. Blueprint search for
`local fibre dimension` returned 24 blueprint nodes, none a definition of this
notion. `blueprint_refs.py ancestor` reports `None` for this item; the new node
records that result and prepends the item to its existing `via` chain.

## Repair of returned delivery 25773a0e885b

H2 is repaired by adding `def-sfb-space-local-fibre-dimension` as described above
and replacing `lem-sfb-space-local-fibre-dimension-open` with that new definition
node in the item's `stmt_deps`. The existing source is imported through the same
module, so the delivered Lean file stays byte-identical (SHA-256
`ba7b840b9c5caed7df71dac857d2a7f0f8c85b2348786cd91230e92cf4e450f8`).
The source main branch still has no Lean record on the item and the original nine
statement dependencies. The repaired packet differs from main only by this item
record, the single added definition node, the item's module, and this report;
`deliver2.py` builds it on the current main branch. This is a substantive dependency
repair, not an unchanged re-push.

Second reading of the repair by Q46: reopened the new node, the existing definition,
and the item. The new node's chart type, affineness, representable étaleness, point
lift equality, distinguished scheme-fibre point, neighbourhood dimension, and
supremum all match the existing definition. It imposes no additional hypotheses.
The item's only new statement dependency is now a definition node. The pre-existing
chart-independence/openness theorem and its proof remain untouched; no theorem is
used by choice to construct the local dimension. The review's other accepted
clauses remain exactly the same in Lean. Independent review remains the maintainer's
responsibility, as the dispatcher forbids starting another agent.

Repair validation: the explicit `scompile.py` run passed sandbox and library-module
compilation in 1.5 seconds each. The repaired `deliver2.py --no-push` also compiled
the existing-declaration probe and printed `OK (dry run): commit cf89446de19 passes
the preflight and compiles; nothing pushed`. No errors or unexpected warnings.
