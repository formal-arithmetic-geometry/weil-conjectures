## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceComponentGenericChartDimension` states
`AlgebraicGeometry.AlgebraicSpace.component_generic_chart_dimension`, with its only proof
`sorry`. No definitions or additional theorem declarations are introduced. The node is
unchanged except for its `lean` record. Its seven proof steps are reproduced in the
statement docstring, including their dependency citations and source places.

The supplied example `Sheaf/CategoryTheory/CompactObject.lean` is now withdrawn and has
no declarations. The new file follows the module header, public section, source docstring,
namespace, and import conventions in the current algebraic-space statement modules.

### Hypothesis and conclusion correspondence

| Node text | Lean rendering |
| --- | --- |
| k is a field | `{k : Type u} [Field k]`; no restriction on characteristic. |
| Y is an algebraic space over Spec k | `Y : AlgebraicSpace (Spec (CommRingCat.of k))`; the recorded category includes the fppf sheaf, representable diagonal, and existence of a representable surjective etale scheme atlas. |
| Y is quasi-compact, in the covering sense specified by the node | `hqc : CompactSpace (Point Y.obj.obj)`; Mathlib's compactness does not include a Hausdorff hypothesis. |
| Y is locally of finite type on etale scheme charts | `hft : ∀ (U : Over (Spec (CommRingCat.of k))) (a : yoneda.obj U ⟶ Y.obj.obj), IsEtale a → LocallyOfFiniteType U.hom`. This quantifies over every scheme-source etale chart, without a surjectivity or compactness restriction. Together with hqc it is precisely the expanded finite-type hypothesis in the node. |
| The diagonal is quasi-compact on scheme tests | `hdiag : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj))`. The product is in presheaves on schemes over Spec k, so this is the diagonal over the stated base. Representability supplies representing scheme pullback squares; `QuasiCompact` means compact inverse images of compact opens. The property is invariant under the unique isomorphisms between representations. |
| Give the point space its atlas topology | The instance `AlgebraicSpace.pointTopologicalSpace` on the recorded `Point Y.obj.obj`, imported from `AlgebraicSpacePointTopology`, is the final topology of all representable etale scheme-source maps. |
| Every irreducible component C | `C : Set (Point Y.obj.obj)` and `hC : C ∈ irreducibleComponents (Point Y.obj.obj)`; Mathlib components are maximal nonempty irreducible subsets and hence closed. |
| Unique generic point eta_C, characterized by closure of its singleton equal to C | The first conjunct is `∃! η : Point Y.obj.obj, closure ({η} : Set (Point Y.obj.obj)) = C`. No sobriety instance is assumed: this is a conclusion. |
| dim C belongs to the nonnegative integers | The second conjunct is `∃ n : ℕ, topologicalKrullDim C = (n : WithBot ℕ∞)`. This excludes both the empty-space dimension bottom and infinite dimension. |
| Every representable etale scheme-source map a:U -> Y | The last conjunct quantifies over `U : Over (Spec (CommRingCat.of k))`, `a : yoneda.obj U ⟶ Y.obj.obj`, followed by `IsEtale a`. The existing IsEtale includes representability. |
| Every u with a(u)=eta_C | It quantifies over `x : U.left`, with `schemePointMap a x = η`. The point map is the existing residue-field representative map, not an auxiliary arbitrary map. The outer eta quantifier has the condition `closure {η} = C`, so this ranges over exactly the generic point supplied by the first conjunct. |
| dim_u U = dim C | `topologicalKrullDimAt x = topologicalKrullDim C` for each such point and chart. |
| C has its subspace topology | `C` is used as the subtype type argument to `topologicalKrullDim`; `instTopologicalSpaceSubtype` is the induced topology. |
| Topological Krull dimension and local dimension | `topologicalKrullDim` is the supremum of strict-chain lengths of irreducible closed subsets, valued in `WithBot ℕ∞`; `topologicalKrullDimAt` is the infimum of this dimension over open neighborhoods, exactly as in its recorded upstream definition. |
| No smoothness, reducedness, separation, geometric irreducibility, or equidimensionality | None is a binder, instance, or premise of the theorem. In particular, hdiag is only quasi-compactness of the diagonal, not separatedness. |

All universes and variables are explicitly bound; `set_option autoImplicit false` is active.
The field and test schemes use the universe of the recorded algebraic-space framework.
Their point-class quotient is in Type (u+1), as defined by that framework; it has not been
replaced by a smaller carrier. No chart is fixed as part of Y's data.

### Dependency declarations read and used

The signatures and docstrings were read in the recorded source modules, not inferred from
declaration names.

| Statement dependency | Module and declaration |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`, `Field` (CommRing and DivisionRing). |
| def-trf-algebraic-space | `Sheaf.AlgebraicGeometry.AlgebraicSpace`, `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsRepresentableWith`, and `AlgebraicSpace.IsEtale`. |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`. |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`. |
| def-a1-space-point-topology | `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, `AlgebraicSpace.pointTopologicalSpace`; its public dependency `AlgebraicSpacePointClasses` provides `Point` and `schemePointMap`. |
| def-weil-irreducible-components | `Mathlib.Topology.Irreducible`, `irreducibleComponents` and `IsIrreducible`. |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`. A chart is bundled with its base morphism as an `Over` object. |
| def-weil-etale-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`, used by the recorded algebraic-space `IsEtale` scheme tests. |
| def-kun-subspace-topology | `Mathlib.Topology.Defs.Induced`, `instTopologicalSpaceSubtype`. |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`. |
| def-kun-topological-dimension-at-point | `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`. |

The statement dependencies are public imports, including via public import chains. The
recorded proof dependencies with available modules are imported without public visibility:
`AffineFiniteTypeAlgebra.affine_finiteType_algebra_of_field`,
`AlgebraicSpacePointOpenCalculus.point_open_calculus`,
`ReducedClosedSubspaceSupport.exists_unique_reduced_closed_subspace`,
`AlgebraicSpaceFibreProductsEtaleCovers.fibreProduct_isAlgebraicSpace` and its companion
pullback statements, `SpaceQuasiCompactAffineTests.quasiCompact_presheafMap_baseChange`
and its comparison statements, `AlgebraicSpaceEtaleOpenImage.etale_open_image`,
`WeilConjectures.AlgebraicGeometry.DenseCompactification.topologicalKrullDim_le_of_dense`,
and `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType.exists_topologicalKrullDim_le`.
Here module prefixes describe where the declarations live; algebraic-space theorem names
are in namespace `AlgebraicGeometry.AlgebraicSpace`.
`IsOpen.topologicalKrullDimAt_eq` is already in the public local-dimension dependency.
Mathlib proof leaves are supplied by imports for affine schemes, quasi-separated morphisms,
finite-type algebras, noetherian prime spectra, noetherian spaces, and topological dimension.
The not-yet-recorded proof prerequisites `lem-sfb-qc-space-affine-etale-atlas`,
`lem-sfb-quasiseparated-space-sober`, `lem-sfb-quasiseparated-space-atlas-dimension`,
and `lem-sfb-etale-topological-dimension-at-point` have no module to import yet. None is
needed to type the statement; their proofs are not replaced by extra premises.

### Source and edge-case checks

Read the local Stacks source for `proposition-reasonable-sober` and
`lemma-dimension-decent-space` in decent-spaces.tex (Tags 03K6 and 0A4J), and
`lemma-dimension-at-a-point-finite-type-over-field` in algebra.tex (Tag 00OT).
The latter explicitly identifies neighborhood dimension with the largest dimension of
components through the point. At a component generic point only that component remains;
the node's finite-component removal and reduced-support argument implements this for spaces.

Checked before writing:

- Empty Y has no irreducible components, so there is no hC and the theorem is vacuous.
- Empty U has no x; no nonempty-chart or surjectivity premise is introduced.
- A non-surjective etale chart is included, as is a non-quasi-compact chart.
- A point component has n=0; no positivity or positive-dimensional premise is imposed.
- For affine n-space at its generic point the local topological dimension is n, whereas
  the local ring dimension is zero. The statement uses the former throughout.
- For a line and a plane meeting in a point, the line's generic point has local dimension
  one, even though the entire space has dimension two. The conclusion uses `dim C`, not
  `dim Y`; the proof removes the other components around the generic point.
- Nilpotent thickenings and all field characteristics are retained. Neither reducedness
  nor perfectness is required.
- The natural-number witness enforces finiteness and nonnegativity even independently of
  whether a particular chart has a point over eta.

No statement dispute, node correction, new nodes, or dependency-interface repairs were found.

### Searches

The prescribed msearch wrapper recorded these queries and results in searches.jsonl:

- `grep`: 'topologicalKrullDimAt|generic.*dimension'. 0 hits. No exact component-generic chart-dimension statement.
- `loogle`: 'topologicalKrullDimAt, irreducibleComponents'. 0 hits. loogle: unknown identifier 'topologicalKrullDimAt' No exact component-generic chart-dimension statement.
- `leanfinder`: 'For a finite type quasi-separated algebraic space over a field, the dimension at a point of an etale chart over a component generic point equals that component dimension'. 8 hits. Returned `Algebra.IsStandardSmoothOfRelativeDimension.out`, `AlgebraicGeometry.Scheme.Etale`, `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`, `Algebra.mem_etaleLocus_iff`, `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`, `AlgebraicGeometry.IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`, `Algebra.etaleLocus`, `Algebra.instEtaleOfIsStandardSmoothOfRelativeDimensionOfNatNat`. No exact component-generic chart-dimension statement.
- `leansearch`: 'dimension at point of etale chart at irreducible component generic point of finite type algebraic space'. 8 hits. Returned `genericPoints`, `genericPoints.ofComponent`, `genericPoints.component`, `genericPoints.isGenericPoint`, `genericPoint`, `genericPoints.isGenericPoint_ofComponent`, `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`, `AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion`. No exact component-generic chart-dimension statement.
- `loogle`: 'topologicalKrullDim, irreducibleComponents'. 0 hits. No exact component-generic chart-dimension statement.

Also searched Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` for `component_generic_chart_dimension`,
`topologicalKrullDimAt.*generic`, and `generic.*topologicalKrullDimAt`.
No existing statement matched. A separate grep for the item id in `lean/WeilConjectures`
returned nothing. A broader generic/chart/dimension source search found scheme geometric
fibre and specialization results, not the present theorem. The searches confirmed the
existing point-class and dimension definitions used above; none was redeclared.

### Validation

The complete module passed the required `scompile.py NL
lem-sfb-space-component-generic-chart-dimension` compilation against the published live
library, both as sandbox source and under its final module name (1.6 seconds each), with no
errors or warnings. The only postponed proof is the named theorem recorded on the node.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
