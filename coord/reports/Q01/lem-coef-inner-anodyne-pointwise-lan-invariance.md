## Worker report

The module `Sheaf.CategoryTheory.InnerAnodynePointwiseLanInvariance` states
`SSet.Enhanced.inner_anodyne_pointwise_lan_invariance`, with one postponed theorem
and three helper definitions containing real data or explicit predicates. No
definition chooses an object from an unproved existence theorem.

Source read: [Kerodon 02YL, Proposition the project server](https://kerodon.net/tag/02YL),
clause (2) and its proof, together with
[Definition the project server](https://kerodon.net/tag/02Y9) (left Kan dual) and
[Warning the project server](https://kerodon.net/tag/02YB). The warning explicitly makes
composition in the functor quasicategory a homotopy class and says that the
colimit condition is independent of its representative. This is why the formal
predicate existentially quantifies the prescribed composition triangle and a
colimiting representative. It does not replace the canonical cocone by an
arbitrary map, and does not assume a strictly selected composition operation.

Hypothesis and clause correspondence:

- The sufficiently large fixed universe is the explicit `universe u`, with
  `L K C D : SSet.{u}`. It is arbitrary; all objects can be placed in that universe.
- The inner-anodyne inclusion is `i : L ⟶ K` and `hi : innerAnodyneExtensions i`.
  This is precisely the dependency's left-lifting definition. No additional
  monomorphism assumption is imposed: inner-anodyne maps are already monic.
- Only `C` and `D` carry `Quasicategory` instances. In particular `L`, `K`, and
  both comma indexing shapes are arbitrary simplicial sets.
- The three diagrams are `δ : K ⟶ C`, `F₀ : K ⟶ D`, and `F : C ⟶ D`.
- The coherent transformation is `β : K ⊗ Δ[1] ⟶ D`. Its whole endpoint
  equalities `hβ₀` and `hβ₁` specify `F₀` and `δ ≫ F`, respectively. These
  hypotheses unpack the given transformation's source and target, rather than
  adding a mathematical restriction.
- `lanIndexSlice δ c` is the actual pullback of `δ` and
  `rightVertexSliceProjection C c`. The latter sends an `(n+1)`-simplex ending
  at `c` to its entire initial `n`-face, and the existing slice operators append
  the last vertex. Thus these are exactly the stated join slices and pullbacks.
- The slice diagram is `pullback.fst δ (rightVertexSliceProjection C c) ≫ F₀`.
- In `IsCanonicalLanCocone`, the triangle `T : lanIndexSlice δ c ⊗ Δ[2] ⟶ D`
  restricts on edge 01 (`stdSimplex.δ 2`) to the actual restriction of `β`.
  Its edge 12 (`stdSimplex.δ 0`) is fixed on every simplex by the existing
  `sliceArrowPrism`, applied to the actual second pullback projection and then
  `F`. This is exactly `F(u)` with all higher compatibility data.
- The long edge 02 (`stdSimplex.δ 1`) is the cocone's whole coherent arrow:
  `t.val` equals the pair consisting of `F.app _ c` and its curried diagram
  vertex. In particular the apex is literally `F(c)`; it is not an existential
  unspecified object. The short-edge constraints rule out unrelated cocones.
- `HasPointwiseLanColimitCocones` quantifies over every vertex `c`, and requires
  `IsColimiting _ t` in exactly the existing coherent comma-cocone convention.
  Existence of a colimiting representative is equivalent to colimitingness of
  any composite with the prescribed two short edges (Kerodon 02YB).
- The conclusion is an `↔`. On the right the inputs are exactly `i ≫ δ`,
  `i ≫ F₀`, the same `F`, and `((i ▷ Δ[1]) ≫ β)`. Restricting a composition
  triangle along the induced slice map preserves both specified short edges,
  its long edge, and the identical apex `F(c)`. Thus the right predicate tests
  the restriction of the same canonical cocone class, not an unrelated cocone.

Recorded dependency declarations read and used:

- `def-cbc-enhanced-diagrams-cones`:
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, especially
  `SSet.Enhanced.diagramVertex`, `appendLast`, `coconeCategory`, and
  `IsColimiting`. The full constructions and endpoint conventions were read.
- `lem-coef-inner-anodyne-pushout-product` is a Mathlib leaf:
  `SSet.innerAnodyneExtensions_pushoutObjObjι'` in
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`.
  Its `innerAnodyneExtensions` is `innerFibrations.llp`; the latter is
  `innerHornInclusions.rlp`. These source definitions and the recorded lemma's
  signature and docstrings were read. There is no repair of this usable match.
- The landed `lem-coef-infinity-slice-arrow-equivalence` is added to
  `stmt_deps` because its owning module `Sheaf.CategoryTheory.SliceArrowEquivalence`
  supplies `SSet.Enhanced.rightVertexSlice`, `rightVertexSliceProjection`, and
  `sliceArrowPrism`. Its node, full module, and docstrings were read. This
  reuses the existing whole-face slice instead of defining another one.

The three already stated proof dependencies are imported without `public`:
`Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`,
`Sheaf.CategoryTheory.InfinityMappingComposition`, and
`Sheaf.AlgebraicTopology.JoyalFunctorEquivalenceTest`. Their recorded declarations
are `SSet.Enhanced.enhanced_functor_cone_calculus`,
`SSet.Enhanced.mapping_composition`, and `SSet.joyal_functor_equivalence_test`.
The repaired delivery adds the recorded statement node
`lem-coef-inner-anodyne-slice-categorical-equivalence` as a statement dependency.
Its module is `Sheaf.CategoryTheory.InnerAnodyneSliceCategoricalEquivalence`, with
declarations `SSet.Enhanced.innerAnodyneSliceIndex`,
`SSet.Enhanced.innerAnodyneSliceMap`, and
`SSet.Enhanced.inner_anodyne_slice_categorical_equivalence`. The latter renders
“categorical equivalence in the Joyal sense” by the exact `hoFunctor` restriction
test recorded by `SSet.exists_joyal_model_structure`; it has no quasicategory
assumptions on `L`, `K`, or either pullback. The target module imports this statement
module so the dependency is available to its future proof.

## New nodes

The returned C1 required the missing Lean statement for the already-recorded node
`lem-coef-inner-anodyne-slice-categorical-equivalence`. I copied that node unchanged
except for its permitted `lean` record and added the module above. The module uses
the canonical existing `rightVertexSliceProjection` and canonical `pullback.map` to
define the slice index and induced map, then states the Joyal `hoFunctor` test with
one `sorry` theorem proof. No new mathematical notion or arbitrary choice is added.

## Dependency modules

The existing node `lem-coef-inner-anodyne-slice-categorical-equivalence` had no
recorded Lean declaration, so this delivery supplies its statement module under the
same node id. The module imports the existing `rightVertexSliceProjection` and the
Joyal model-structure convention, defines the actual pullback and its canonical map,
and states the exact `hoFunctor` restriction equivalence. The target imports this
module as a statement dependency; no dependency statement is weakened or replaced.

Edge cases checked:

- Identity `i`: both sides test the same slice diagrams, apex, and beta.
- `L = K = empty`: slices and their cylinders are empty. The pair equation
  still fixes the apex `F(c)`; initiality in the empty-diagram cocone category
  remains the required condition. No apex data disappear with an empty shape.
- Empty `C`: both universal conditions have no vertex tests. No nonemptiness
  hypothesis was added. Empty `D` is allowed whenever the displayed maps exist.
- At degree zero, the prism sends interval vertices to the original vertex and
  the new final vertex. Hence the two short legs are exactly beta and `F(u)`.
- The horn inclusion `Λ[2,1] → Δ[2]` is admitted without quasicategory
  assumptions on either shape; no ordinary category nerve replaces it.
- All simplex degrees and all interval simplices occur in the edge-12 formula,
  so it does not merely specify the cocone's vertex components.

Searches performed for this assignment:

- `msearch.py leanfinder`: "Pointwise left Kan extension cocones of
  quasicategories invariant under inner anodyne change of simplicial indexing
  shape". Eight hits: ordinary categorical Kan extensions and the StrictSegal
  coskeletal right Kan extension. None is this assertion.
- `msearch.py loogle`: `SSet.innerAnodyneExtensions`. Twelve hits give the
  lifting-class definition, closure instances, and horn/cellular facts. None
  states the pointwise cocone invariance theorem.
- `msearch.py grep`: `innerAnodyne|KanExtension`, restricted to
  `AlgebraicTopology/Quasicategory`. Zero hits.
- `msearch.py leansearch`: "Left Kan extension of a quasicategory diagram is
  invariant under inner anodyne changes of simplicial indexing set". Eight
  hits concern ordinary categorical Kan extensions; none matches.
- Direct `rg` in the upstream `WeilConjectures` source for the item id and
  `inner.anodyne.*[Kk]an|[Pp]ointwise.*[Ll]an`: no match.
- Direct `rg` in `lean/Sheaf/CategoryTheory` and `AlgebraicTopology` found the
  existing slice and prism APIs, the coherent comma construction, and later
  pointwise Kan-restriction predicates. These were inspected; none states this
  arbitrary-shape invariance theorem. Direct name search in Mathlib, upstream,
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found none of the four new names.
- A dependency-closure check confirms that the added slice owner cannot reach
  this item. The later `KanMappingRestriction` module can reach this item, so
  its specialized helper definitions were not imported. No dependency cycle
  is introduced by the added statement dependency.

No statement correction, new DAG node, dependency repair, or disputed statement
is needed. Q05's reviewed record is a stage-1 split and carries no `lean` record;
it does not supersede this stage-2 statement assignment. The item copy changes
only `lean` and the permitted addition of the landed slice owner to `stmt_deps`.

Validation: `scompile.py Q01 lem-coef-inner-anodyne-pointwise-lan-invariance`
compiled this module both in its private sandbox and under its library module
name, with no errors or warnings. All universes and variables are explicit;
the only postponed proof is the theorem named above.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
