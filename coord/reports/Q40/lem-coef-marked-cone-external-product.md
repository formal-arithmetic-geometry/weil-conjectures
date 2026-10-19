## Worker report

The module `Sheaf.AlgebraicTopology.MarkedConeExternalProduct` states
`SSet.MarkedCone.marked_cone_external_product : Nonempty ExternalProductStatement`.
Its sole theorem has proof `sorry`. All definitions have real data. The theorem
packages the marked-cone construction and its uniquely normalized comparison,
without selecting any definition from the theorem's unproved existence assertion.
The thirteen proof paragraphs from the node are included in the theorem docstring.
No statement correction or disputed statement is needed.

Source checked: Lurie's *Higher Topos Theory*, Definition the project server, Notation
the project server, and Proposition the project server, PDF pages 188–189 and 193–194,
https://www.math.ias.edu/~lurie/papers/HTT.pdf (read online 2026-10-17).
Proposition the project server quantifies over arbitrary simplicial categories and asserts
that the projection comparison is a weak equivalence of projective diagrams.
No local Kan hypothesis is present. The existing node already expands the
source's omitted explicit calculation and its two-variable induction.

The statement is encoded clause by clause as follows. Names below are in
`SSet.MarkedCone` unless otherwise qualified.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small simplicial sets S and S' | `S T : SSet.{u}`, with `universe u` explicit. |
| Small simplicial categories I and I' | `I J : CategoryTheory.CoherentNerve.SCat.{u}`: actual enriched categories with object types in `Type u` and mapping objects in `SSet.{u}`. |
| Simplicial functors C[S] → Iᵒᵖ and C[S'] → (I')ᵒᵖ | The binders `u` and `v` of `productFunctor` and `ComparisonFamily`, using `PinchedCube.rigidification` and `UnmarkedStraightening.oppositeCategory`. |
| Marked objects X → S and X' → S' | `X : Input S`, `Y : Input T`, where `Input S` is the existing slice `Over (Marked.sharp S)`. A map to the sharp marking imposes no restriction on the marking of its domain. |
| P_X = Iᵒᵖ amalgamated with C[X ⋆ Δ⁰] over C[X] | The existing `UnmarkedStraightening.conePushout I u (underlyingInput X)`. Its two actual pushout legs are `baseInclusion` and `coneInclusion`. Its attaching map is `rigidification.map X.hom.val ≫ u`. |
| New cone vertex v | The existing `UnmarkedStraightening.coneVertex I u (underlyingInput X)`, the image of the pure last block of the ordered join. |
| L_u(X)(i) = P_X(i,v) | `markedValue I u X i` has underlying simplicial set exactly `UnmarkedStraightening.value I u (underlyingInput X) i`. |
| The cone edge tilde-e associated to e | `edgeTriangle` is C[Δ²] → C[X ⋆ Δ⁰] → P_X. In `markedValue.marking`, `p` is the edge in its mapping interval whose endpoint paths have subsets `{0,2}` and the full set `{0,1,2}`. Its image is the coning edge. |
| Mark g*tilde-e for each marked e and every degree-one old arrow g | The existential marking clause requires `e ∈ X.left.marking`, chooses the source coefficient `d = coefficientVertex I u (X.hom.val.app _ (X.left.underlying.δ 1 e))`, and includes exactly `valueAction ... d i (t,g)` for every `g : (hom I d i) _⦋1⦌`. This is Iᵒᵖ(i,u(x)) with the opposite reversed. |
| Include all degenerate edges | The other marking clause is `Set.range (value ... i).σ 0`; the structure's `degenerate` field explicitly injects this range. |
| Precomposition gives the full simplicial I-action | The existing `UnmarkedStraightening.valueAction`, including all mapping simplices. `underlying_diagrams` realizes these values and actions by an actual existing `UnmarkedStraightening.Diagram I`, hence an `EnrichedFunctor SSet I SSet`. |
| Acting mapping spaces have every edge marked | `ExternalProductStatement.action_marked` uses `Marked.product (markedValue ... i) (Marked.sharp (hom I i k))`. The value-first order is the recorded unmarked action's convention; its braiding is the source's precomposition order. |
| Functoriality in the marked input | `underlyingInputMap` is the actual forgotten map of slice objects; `input_maps_marked` asserts that its existing `valueMap` preserves the prescribed markings. The identity/composition laws are those of the existing canonical pushout maps. |
| Product index I × I' | `productIndex I J`, with object set literally `I × J`, mapping simplicial set `hom I ... ⊗ hom J ...`, coordinatewise identity and composition. Its data and laws are written in full. |
| u box u' induced by both projections | `productFunctor I J u v`: the two components are exactly `rigidification.map (fst S T) ≫ u` and `rigidification.map (snd S T) ≫ v`, on objects and every mapping simplex. |
| Marked product X × X' over S × S' | `productInput X Y`, built from the existing `Marked.product` and the actual tensor product of the two base maps. Its marking is the coordinatewise product marking. |
| G box H has values G(i) × H(i') | `Marked.product (markedValue I u X i) (markedValue J v Y j)` in the codomain of `ComparisonFamily.comparison`. `externalAction` is the coordinatewise product action. |
| Projections induce the canonical comparison | `ComparisonFamily.first` and `.second` are enriched pushout maps fixed by `first_base`, `first_cone`, `second_base`, `second_cone`. Each fixes its old-base leg by the appropriate index projection and its cone leg by the corresponding input projection. The pushout universal property determines each map uniquely. |
| The map on diagram values is the induced map on homs to v | `first_value` and `second_value` identify the projections of `comparison.val` with the two actual enriched hom maps of those pushout functors. `HEq` records only equality transport of pushout endpoint objects, and specifies the entire simplicial map, not just vertices. |
| A map of marked (I × I') diagrams | `comparison` is a marking-preserving morphism in `SSet.Marked`; `enriched_naturality` is equality of full simplicial action maps for every `i,k : I`, `j,l : J`, rather than ordinary vertex naturality alone. |
| Natural in X and X' | `input_naturality` is the commuting comparison square for every pair of slice arrows `f` and `g`, using the actual `UnmarkedStraightening.valueMap` and `productInputMap`. |
| Objectwise weak equivalence in the absolute marked Cartesian model | `ComparisonFamily.objectwise_weak` asserts `Marked.weak (comparison X Y i j)` for every pair `(i,j)`. This is exactly the recorded absolute mapping-test weak equivalence, not the unmarked weak homotopy-equivalence predicate. |
| No local Kan hypothesis on either index | There is no `IsLocallyKan`, horn-filling, fibrancy or other constraint on `I` or `J` anywhere in the binders. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CoherentNerveComparison`: the full signature and docstring
  of `coherent_nerve_comparison`, and the `SCat`/`hom` convention it imports from
  `Sheaf.CategoryTheory.CoherentNerveInfrastructure`.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `SSet.Marked`, its actual
  category, `sharp`, `product`, `productMap`, and `weak`. The theorem
  `marked_point_cartesian_model` identifies that weak class with the absolute
  Cartesian model; it adds no parameter to the present theorem.
- `Sheaf.CategoryTheory.SimplicialProjectiveModelCalculus`: the recorded
  `simplicial_projective_model_calculus`, including objectwise projective weak
  equivalences and full enriched-diagram transformations, without local Kan
  restrictions. This is retained as a public statement-dependency import.
- `Sheaf.AlgebraicTopology.UnmarkedStraighteningQuillen`: `oppositeCategory`,
  `Diagram`, `action`, `conePushout`, `baseInclusion`, `coneInclusion`,
  `baseObject`, `coneVertex`, `value`, `valueAction`, `valueMap`, and
  `coefficientVertex`. These are reused exactly rather than copied.
- `Sheaf.AlgebraicTopology.PinchedCubeLatching`: `coherentSimplex`,
  `rigidification`, and `coherentSimplexUnit`, the recorded subset-poset
  realization and its simplex-colimit extension. Ordered-join maps and
  `joinPointTopSimplex` are the existing `SSet.Enhanced` constructions imported
  by these modules.

The last two already-landed nodes are added to `stmt_deps`, as allowed by
brief-stage2 §5 for landed notions. No other original node field changes.
The product, marked-value and comparison helper declarations belong to the
constructions explicitly introduced in this item's own statement; no independent
missing notion, new definition node or dependency repair is introduced.

All already-stated proof dependencies are imported with non-public `import`
(unless already imported publicly for the statement). This includes the Mathlib
boundary-cell and small-object modules for their recorded Mathlib matches.
`lem-coef-marked-cone-generator-calculations` currently has no Lean record, so
there is no module to import; it remains the existing proof prerequisite and its
use is retained in the proof docstring. It is not needed to type this statement.
`MappingSimplexConeFibers` was inspected but is not imported: its proof depends
on this item. Its special-case marked cone definition is not a general-index
interface and cannot serve here without an import cycle. The present module
uses the earlier generic unmarked cone pushout and specifies its marking directly.

Edge cases checked:

- Empty S or T: a slice object over an empty simplicial set has empty domain;
  the old categories and the new cone vertex are still retained. No chosen
  vertex of either base occurs in the top-level construction.
- Empty I or J: the given indexing functor forces the corresponding base empty;
  the comparison's component quantification is empty. No inhabitance assumption
  is introduced by the product category or cone pushout.
- Empty X or Y: both cone values in the comparison have the initial marked value
  on the empty side; the comparison has the expected empty-source/empty-target
  case. The definitions do not invent a cone generator when no edge exists.
- Point inputs: degeneracies are included explicitly. Their precomposites mark
  all acting edges as required for the free sharp representable, not only the
  degenerate acting edges.
- Flat and sharp single edges, including marked degeneracies: the coning interval
  is directed from `{0,2}` to `{0,1,2}`, exactly tilde-e in HTT. The marking clause
  tests the original marked edge and allows every acting degree-one simplex.
- Non-Kan mapping simplicial sets: no replacement of the indexing category is
  used. All raw enriched mapping objects remain unchanged.
- Universes: the arbitrary universe `u` contains both small bases, indices,
  mapping objects and marked inputs. No restriction equates unrelated site
  object/morphism universes; this is the usual one-universe meaning of small
  simplicial categories in the node. All binders are explicit and
  `autoImplicit` is false.

Searches made with the prescribed wrapper:

- LeanFinder, `marked cone diagram external product weak equivalence`: eight
  hits, ordinary categorical cone constructions, not marked straightening.
- LeanSearch, `Marked straightening external products simplicial sets`: eight
  hits for products of simplicial subcomplexes and standard simplices, ordinary
  tensor/unit formulas and nondegeneracy; no marked cone comparison.
- Loogle, `CategoryTheory.EnrichedFunctor, SSet`: three hits,
  `SimplicialThickening.functor`, `.functor_id`, `.functor_comp`. These supply
  coherent simplex functors, not this marked product theorem.
- Loogle, `SSet Marked external product`: parser rejection/no hits; replaced by
  the valid enriched-functor query above.
- Mathlib grep, `Marked|SimplicialCategory|EnrichedFunctor` in CategoryTheory:
  eighteen hits concerning basic enriched functors and unrelated occurrences
  of 'marked'; none is the desired comparison or product enrichment.
- Mathlib grep, `markedCone|MarkedCone|external.{0,20}product|straighten` in
  AlgebraicTopology: three hits, ordinary two-truncated edge external products
  and `SSet.Subcomplex.prod`; none is marked cone straightening.
- Direct `rg` of the upstream `WeilConjectures` tree, the project `lean/Sheaf`
  tree, and `dag/lean_names_upstream.json` for the item, `MarkedCone`,
  straightening, product and enriched-product names: no existing statement.
  The generic cone/value/action declarations listed above were found and reused.
  The specialized `MappingSimplexConeFibers` declarations were read and the
  dependency cycle was checked before deciding not to import that later theorem.
- The explicitly requested `grep -rn` for the item id in upstream
  `WeilConjectures` returned no declaration.

Validation: the entire module, including the final theorem and every definition,
compiled with `scompile.py Q40 lem-coef-marked-cone-external-product` under the
normal 60-second limit. Both sandbox and named-module passes were clean, without
warnings. The theorem is the only postponed proof in the delivered source.
The required `deliver2.py Q40 lem-coef-marked-cone-external-product --no-push`
dry run printed `OK (dry run)` for commit `1485d4c75c`: compilation and preflight
passed except for the independent second reading, which the second reader writes.
Nothing was pushed. No second-reading section has been supplied by this worker.

## Second reading by Q40

I read `AGENTS.md`, `SETUP.md`, the stage-2 brief and delivery-errors H, the
item node, its chapter/unit route, the worker report, every recorded statement
dependency, and the current source module. I also read HTT Definition the project server,
Notation the project server and Proposition the project server in the official HTT PDF (PDF pages
188--194; printed pages 171--177). The source is HTT rather than a Stacks tag.

The node's statement, item by item, and the Lean verdicts are:

1. Small simplicial sets `S,S'`, small simplicial categories `I,I'`, the two
   coefficient functors, and marked maps over the bases are rendered by the
   explicit universe-`u` binders of `productFunctor`, `Input`, and
   `ExternalProductStatement`; PASS. No local Kan, fibrancy, or nonemptiness
   hypothesis is added.
2. The cone pushout `Iᵒᵖ ⨿_{C[X]} C[X ⋆ Δ⁰]`, its cone vertex, and the values
   `P_X(i,v)` are exactly the existing `conePushout`, `coneVertex`, and `value`
   declarations in `UnmarkedStraighteningQuillen`; PASS. The module does not
   define a private replacement.
3. The marked cone edges and all degeneracies are rendered by `edgeTriangle`
   and `markedValue`: the interval endpoints are the direct and full subsets,
   marked input edges are precomposed by every degree-one `hom I d i` simplex,
   and `Set.range (value.σ 0)` supplies all degeneracies; PASS.
4. The full simplicial action and its marking preservation are rendered by
   `valueAction`, `externalAction`, and `ExternalProductStatement.action_marked`;
   PASS. The sharp mapping factor marks every acting edge, exactly as in HTT.
5. Functoriality in input maps is rendered by `underlyingInputMap`,
   `productInputMap`, and `input_maps_marked`; PASS. The equations use the
   canonical `valueMap`, so they are the source's pushout-induced maps.
6. The product index has object type `I × J` and coordinatewise enriched
   mapping object, identities and composition in `productIndex`; PASS.
7. The product coefficient functor is `productFunctor`, whose two components
   are the rigidifications of the projections followed by `u` and `v`; PASS.
8. The marked product input is `productInput`, using the tensor product of the
   base maps and `Marked.product`'s coordinatewise marking; PASS.
9. The target external product values and action are the marked products in
   `ComparisonFamily.comparison` and `externalAction`; PASS.
10. The two canonical projections are fixed by all four pushout-leg equations
    (`first_base`, `first_cone`, `second_base`, `second_cone`); PASS. Their maps
    on values are the actual mapping simplicial maps, with only endpoint
    equality transports (`first_value`, `second_value`).
11. The comparison is a morphism of marked objects, is enriched-natural on all
    mapping simplices (`enriched_naturality`), and is natural in both inputs
    (`input_naturality`); PASS. This is stronger than ordinary vertex-only
    naturality and agrees with the source's canonical comparison.
12. `objectwise_weak` states `Marked.weak` at every `(i,j)`, which is the
    absolute marked Cartesian weak-equivalence conclusion; PASS.
13. `comparisons` packages the comparison family for every pair of indices and
    coefficient functors as `Nonempty`, so no arbitrary comparison is selected
    by a definition; PASS. The sole theorem is postponed with `sorry`.

Edge cases checked: empty bases and empty inputs retain the cone construction
and give the initial values; empty index categories impose no hidden inhabitance
condition; vertices give the free sharp representable; flat, sharp and mixed
single edges give the prescribed coning markings; degenerate edges are included;
loops and identified endpoints are allowed; `n=0` is covered by the degeneracy
clause; non-Kan mapping spaces are allowed; and all objects remain in the one
explicit small universe. No characteristic or algebraic hypothesis is present
or needed.

Searches were repeated with the required wrapper: LeanFinder, LeanSearch,
Loogle, Mathlib grep, and source/project/DAG `rg` searches for marked cone,
straightening, enriched product and the exact item id. Results were ordinary
category cones, products of simplicial sets, and homotopy-category products;
none was this marked straightening comparison. The existing declarations found
(`Marked`, `product`, `sharp`, `weak`, coherent nerve infrastructure, and the
unmarked cone pushout/value/action) were opened and reused. No duplicate
definition or statement exists in Mathlib, the source checkout, or this DAG.

Mismatches found: none. I did not alter the node statement, dependencies,
definitions, or theorem signature. The only delivery change is this independent
second-reading record. The module recompiles cleanly with the required
`scompile.py` wrapper; the theorem is the only `sorry`, and no warnings remain.
