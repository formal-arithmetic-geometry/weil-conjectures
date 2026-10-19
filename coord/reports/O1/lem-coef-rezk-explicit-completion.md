## Worker report

The delivery states `CategoryTheory.SegalSpace.rezk_explicit_completion` in
`Sheaf.CategoryTheory.RezkExplicitCompletion`. Its only postponed theorem is that
statement, with whole proof `by sorry`; its docstring contains all eight proof
steps of the DAG node with their dependencies. All definition and structure data
are explicit. The definition-only module `Sheaf.CategoryTheory.SegalSpace`
belongs to the new node `def-coef-segal-space`.

I read the item, its three statement dependencies and their recorded source
declarations, the stage-2 brief and error list, and Rezk's Sections 4--6 and 14
(pp. 11--14 and 32--34), including the construction before Remark 14.1. The
item's mathematical statement and proof are unchanged. Only `lean` and the
addition of the new definition node to `stmt_deps` change on the item.

The inherited sandbox contained a working core of the explicit construction,
but no node owning its separate SegalSpace module, a failing auxiliary
exponential equivalence, and metadata/report describing a different earlier
`Nonempty (RezkCompletionData W)` statement. I removed the unnecessary auxiliary
equivalence and used the existing Mathlib internal hom directly. The theorem is
universal in a chosen `ReedyReplacement`; an existential choice would lose the
source's independence of the chosen replacement and is not the delivered form.

The following matches every hypothesis, convention and conclusion of the item.
All names in the table have namespace `CategoryTheory.SegalSpace` unless qualified.

| Node text | Lean rendering and check |
| --- | --- |
| Small simplicial space `W : Δᵒᵖ → sSet` | `W : Space.{u}`, where `Space` is `SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ Type u`; `Functor.curry` gives the stated simplicial object in simplicial sets, with no restriction on the small universe `u`. |
| Reedy fibrant | `IsReedyFibrant W` tests `Reedy.matchingFrom (monomorphisms SimplexCategory).op (Functor.curry.obj W) n` against the actual Kan horn-lifting class `SSet.modelCategoryQuillen.J.rlp`. Opposite-injective simplex maps are the negative Reedy maps. |
| Consecutive-edge weak equivalences for all `n ≥ 2` | `hW : IsSegal W` is that Reedy predicate conjoined with `∀ n, 2 ≤ n → Enhanced.IsWeakHomotopyEquivalence (segalMap W n)`. `chains` is `SSet.Path` in each inner degree, retaining its vertices and consecutive edges. This is the iterated strict fibre product, not an arbitrary equivalent target. `segalMap` is `SSet.spine` with the actual consecutive restrictions. |
| Strict mapping fibre `M_W(x,y)` | `endpoints` is the pair of outer faces `(δ 1, δ 0)`; `mappingSpace` is its strict Mathlib pullback along the constant point `(x,y)`. `mappingSpaceMap` is `pullback.map` using the degree-one and degree-zero components of the given map, with the identity on the point. No mapping-space comparison is supplied as arbitrary data. |
| Homotopy-category isomorphisms | `SameMappingComponent` uses equality under `SSet.π₀.mk` inside that strict fibre. `IsEquivalenceArrow` asks for one inverse edge and two outer triangles, with their long edges equal to the respective identity components. For a Reedy fibrant Segal space the degree-two Segal map is a trivial fibration, so such triangles exist exactly for composable representatives; their component is the prescribed homotopy-category composite. Thus these are exactly the two inverse equations in `hW`, without choosing a composition or a private homotopy category. |
| Union `W_eq` of invertible components | `equivalenceArrows` uses the recorded `Enhanced.fullSubcomplex` on the vertices in components of `W₁` containing an `IsEquivalenceArrow`. Equality of `π₀` classes saturates whole components. Its simplices are exactly those whose vertices are in these components. |
| Complete means the actual `s₀ : W₀ → W_eq` is a weak equivalence | `IsComplete` includes `IsSegal` and a factor `s` through the subcomplex inclusion, with equation `s ≫ ι = W.map (σ 0).op` and `Enhanced.IsWeakHomotopyEquivalence s`. The inclusion is mono, so the factor is unique; it cannot be an arbitrary equivalence between the two objects. |
| Groupoid `I[m]` has `m+1` objects and one arrow per ordered pair | `equivalenceResolution` composes `SimplexCategory.toCat`, `Cat.objects`, `uliftFunctor`, `Codiscrete.functorToCat`, `nerveFunctor` and `outerDiscrete`. Its object set is a universe lift of `Fin (m+1)`. Mathlib's `Codiscrete` has exactly `Unit` morphisms between each pair and hence is the required groupoid. |
| `E(m)` is the outer nerve, inner-discrete | The last component `outerDiscrete` is precomposition with `Prod.fst`; inner operators act as identities. The whole composite is cosimplicial, using the actual monotone map on vertices. |
| `F(n)` and `cK` | `outerRepresentable := SSet.stdSimplex ⋙ outerDiscrete`; `innerConstant` is precomposition with `Prod.snd`. |
| The cartesian exponent formula and its operators | `powerResolution` uses Mathlib's `MonoidalClosed.internalHom`. Its implementation in `FunctorToTypes.rightAdj` is `Functor.functorHom`; evaluation is `HomObj` on the covariant representable of the product index. `Functor.homObjEquiv` identifies this with maps `A × F(n) × c Δ[q] → W`. Restriction of the representable arguments gives exactly the two precomposition operators. No second internal-hom definition is introduced. |
| Diagonal `W̃_(n,q) = (W^E(q))_(n,q)` | `resolutionDiagonalIndex.obj (n,q) = (q,(n,q))` and its map sends `(α,β)` to `(β,(α,β))`. `resolutionDiagonal` uncurries and precomposes by this index; `tilde := powerResolution ⋙ resolutionDiagonal`. Thus the resolution and inner operators act simultaneously. |
| Collapse map `W → W̃` | `powerResolutionUnit` curries the second projection `E(m) × W → W`, which is exactly precomposition with the unique collapse. `constantResolutionDiagonalIso` identifies the diagonal of the constant resolution with `W`, and `tildeUnit` is its composite with that unit's diagonal. |
| Choose a functorial Reedy replacement `W̃ → Ŵ` | The explicit binder `R : ReedyReplacement.{u}` carries a functor, its unit natural transformation, actual Reedy-fibrancy proofs and levelwise realization-based weak equivalences. This packages exactly the permitted choice; no unrelated map or stronger condition such as a prescribed degree-zero factorization is assumed. Its existence is supplied by the recorded Reedy model-structure and Kan factorization dependencies. |
| `Ŵ` and `i_W` are the specified composites | `completion R := tilde ⋙ R.functor`; `completionUnit R := tildeUnit ≫ whiskerLeft tilde R.unit`. |
| `Ŵ` is complete Segal | First conjunct `IsComplete ((completion R).obj W)`. This includes the complete condition and the Segal condition with Reedy fibrancy. |
| Every actual mapping-space comparison is a weak equivalence | The second conjunct quantifies over all vertices `x y` of `row W 0` and applies `Enhanced.IsWeakHomotopyEquivalence` to `mappingSpaceMap ((completionUnit R).app W) x y`. |
| Every object of `hŴ` is isomorphic to some image | `IsEssentiallySurjective ((completionUnit R).app W)` quantifies over every target vertex, and gives a source vertex and an equivalence arrow from its actual image to that vertex, with both endpoint equalities. |
| Naturality in maps of Segal spaces | `completion R` is an actual functor on all simplicial spaces and `completionUnit R` is a natural transformation. Restriction to Segal objects gives exactly the asserted naturality; it is not replaced by objectwise choices or a separate unconstrained naturality predicate. |

Statement dependency interfaces read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: the recorded
  `SSet.Enhanced.IsWeakHomotopyEquivalence` and `fullSubcomplex`, with the
  realization-based component and based homotopy-group definition.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen`, especially its agreement of
  fibrations with `SSet.modelCategoryQuillen.J.rlp`, Kan fibrant objects and
  functorial factorizations. The matching predicate uses precisely that horn class.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.matchingFrom`, `matchingProjection`, `model_structure`
  and the simplex Reedy interface; the node's functorial replacement choice is
  packaged explicitly as `ReedyReplacement` without extracting data from a
  sorry-backed mere existence statement.
- New `Sheaf.CategoryTheory.SegalSpace`: `IsSegal`, `mappingSpaceMap`,
  `IsComplete`, `IsEssentiallySurjective`, and their listed helper definitions.

The six currently stated proof-only interfaces are imported without `public`:
`RealizationFiniteLimits`, `KanFibrationArbitraryBaseFibers`,
`KanHomotopyPullbackInvariance`, `RealizationCylinder`,
`HomotopyGroupsBasepointChange`, and `BisimplicialDiagonalEquivalence`.
The Reedy and Kan interfaces are already visible through the statement imports.
The other proof dependency nodes have no Lean record yet and are therefore not
imported: `lem-coef-segal-cartesian-exponent`,
`lem-coef-segal-categorical-equivalence-dk`, `lem-coef-space-geometric-descent`,
`lem-coef-equifibered-bisimplicial-diagonal`, and
`lem-coef-segal-equivalence-classifier`.

Edge cases checked before finalizing the statement:

- No nonemptiness of `W₀` is assumed; the empty simplicial space is included and
  the quantification over mapping objects is vacuous only when there are no objects.
- The Segal condition starts at `n = 2`; `chains` is still defined for `n = 0,1`,
  and Reedy fibrancy is tested also at degree zero (empty matching diagram).
- `I[0]` has exactly one object and is the terminal groupoid. No inverse or
  nonempty-index choice has been substituted for the collapse in degree zero.
- Identity and degenerate outer edges use the actual `σ 0`; inverse equations
  are inside fixed-endpoint mapping fibres, not merely in components of `W₁`.
- The noncomplete discrete nerve of a groupoid is allowed by `IsSegal`; it is
  not accidentally required to be complete as a hypothesis. Complete discrete
  examples and categories with noninvertible arrows distinguish the two predicates.
- Universe `u` is arbitrary, including zero. Finite indexing and the `ULift` in
  the codiscrete resolution do not impose equalities with any site universes.
- `R` ranges over every functorial Reedy fibrant replacement with the stated
  levelwise weak equivalence, not just one specially normalized replacement.

Searches made (all remote searches are logged in `searches.jsonl`):

- `msearch.py leanfinder`, query `Rezk completion of a Reedy fibrant Segal space
  using nerves of codiscrete groupoids`: 8 hits on ordinary nerves/strict Segal
  simplicial sets, no Rezk completion theorem.
- `msearch.py loogle`, query `Segal, Rezk`: 0 hits with diagnostic
  `unknown identifier 'Segal'`; this is not evidence of an existing declaration.
- `msearch.py grep`, query `SegalSpace|Rezk|complete Segal`: one unrelated
  reference to Rezk in `CategoryTheory/LiftingProperties/PushoutProduct.lean`.
- For the new definition, `msearch.py leansearch`, query `A Segal space is a
  Reedy fibrant simplicial space with weak equivalence consecutive edge maps`:
  8 hits for `SSet.StrictSegal`, `IsStrictSegal` and their API. Those concern
  bijective spine maps of set-valued simplicial sets, not Reedy fibrant
  simplicial spaces with weak-equivalence spine maps.
- For the new definition, `msearch.py leanfinder`, query `Segal space Reedy
  fibrant simplicial space weak equivalence spine maps and complete Segal space`:
  8 further strict-Segal API hits, no matching notion.
- For the new definition, `msearch.py grep`, query
  `IsSegal|SegalSpace|CompleteSegal|complete Segal`: 0 Mathlib hits.
- `rg` on `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the shared
  `lean/Sheaf` for `SimplicialSpace|IsSegalSpace|RezkCompletionData|rezk_explicit_completion`,
  then `simplicial space|SegalSpace|Rezk|IsSegal`: no definition or theorem matching
  the item or the Segal-space interface. The two textual hits in the shared
  library describe simplicial spaces of sections/classification diagrams, not
  a Segal-space definition. The required upstream node-id grep returned no hit.
- `dag/lean_names_upstream.json` search for the same notions: no declaration.
- `tools/blueprint_refs.py search 'Segal space'`: 0 blueprint matches;
  `ancestor lem-coef-rezk-explicit-completion` returns
  `prop-coef-integral-exceptional-adjoint`.
- DAG content search found 33 nodes mentioning Segal spaces. The definition
  nodes among them are enriched Segal-presheaf localization and weak operadic
  approximation, not this Reedy fibrant simplicial-space notion. The Rezk local
  model, classifier, exponent, and completion nodes are statements without a
  usable Segal-space declaration; their theorems are not restated here.

There is no statement correction, unusable dependency repair, or
`STATEMENT-DISPUTED` flag. The two delivered files have been compiled separately
in dependency order using only the authorized `scompile.py` wrapper. The worker dry run
`deliver2.py N1 lem-coef-rezk-explicit-completion --no-push` printed
`OK (dry run): commit 72a0f65c1b passes the preflight and compiles; nothing pushed`.
It compiled both delivered files separately and passed server preflight. After that
check, the item copy was refreshed to preserve the automatically updated
`lean_audit` bookkeeping, and a literal paragraph escape in the new-node statement
was replaced by an actual paragraph break. The final packet is checked again below.

## New nodes

`def-coef-segal-space`, in the item's chapter and unit, owns
`Sheaf.CategoryTheory.SegalSpace`. It defines the bisimplicial encoding, rows,
strict mapping fibres and their induced maps, the actual consecutive-edge maps,
Reedy fibrancy, the Segal condition, fixed-fibre component equality, inverse
arrows, their union of components, completeness via the actual degeneracy, and
essential surjectivity. Its source is Rezk Sections 2.3--2.4, 4.1, 5.1--5.8,
6 and 7.4. It contains no postponed theorem. The three new-node search records
contain the actual outputs of the searches named above. The project, DAG and
blueprint searches found no node or recorded declaration already owning this
notion. The item adds this definition node to its statement dependencies.

## Earlier second reading (a previous round; superseded)

To be completed by the independently started second reader. This worker has not
performed or claimed the independent second reading and has not pushed a delivery.

## Second reading by N1

I am the independently started second reader, not the author of these modules.
I read the unchanged base statement and eight proof steps, both sandbox modules,
the new definition node, and the three recorded statement-dependency signatures
and constructions. There is no repair note for this item and no statement_change.
The mathematical statement and Lean declarations needed no repair. I changed
`lean.statement` to retain the theorem signature's exact line breaks and indentation;
the earlier record had normalized it to a single line. Both modules compiled cleanly
through `scompile.py N1 lem-coef-rezk-explicit-completion` in this reading.

Source checked: Rezk, *A model for the homotopy theory of homotopy theory*, the
PDF at the node's URL, Sections 2.1--2.4, 4, 5.1--5.7, 6, 7.4, and Section 14,
printed pages 32--34 (construction before Remark 14.1 and proof of (1),(3)).
This source is not a Stacks result; there is no Stacks tag to substitute.
Section 2 uses simplicial sets as spaces, Section 4 includes Reedy fibrancy,
and Section 14 assumes precisely that W is Segal. No extra nonemptiness,
finite-dimensionality, or pointedness hypothesis is assumed there.

Here is my object/hypothesis/conclusion inventory and its Lean match. Names below
are in `CategoryTheory.SegalSpace`, except where qualified.

| Node item | Lean inspected | Verdict |
| --- | --- | --- |
| Small simplicial space W, outer then inner degree | `Space.{u} := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ Type u`; `row`; `Functor.curry.obj W` | Exact uncurried presentation of Δᵒᵖ → sSet; arbitrary u. |
| Reedy fibrancy | `IsReedyFibrant`, using dependency `HomotopicalAlgebra.Reedy.matchingFrom` for `(monomorphisms SimplexCategory).op` | Exact negative Reedy category: opposite injections, with identities removed by dependency `MatchingIndex`. Tests all degrees, including zero. |
| Actual consecutive-edge Segal maps for every n ≥ 2 | `IsSegal W`, `chains W n`, `segalMap W n` | Reedy fibrancy plus the required weak equivalences. `SSet.Path` retains n edges, n+1 vertices and endpoint equations; `SSet.spine` restricts to consecutive edges. For n ≥ 2 this is the specified strict iterated fibre product. |
| Weak equivalences mean realization equivalences | `SSet.Enhanced.IsWeakHomotopyEquivalence` | Dependency's actual bijection on realized path components and every positive based homotopy group. No substitute class. |
| Objects x,y and mapping fibre | `endpoints W`, `mappingSpace W x y` | Endpoints are `(δ 1, δ 0)`. Pullback is along the constant point `(x,y)` from the actual terminal simplicial set. This is the strict fibre. |
| Mapping-space comparison induced by f | `mappingSpaceMap f x y` | `pullback.map` uses f in outer degrees 1 and 0 and identity on the point; naturality proves the two commuting squares. It is the actual induced map. |
| Morphisms of hW and identity/composition convention | `SameMappingComponent`, `IsEquivalenceArrow` | Equality of `SSet.π₀.mk` in the fixed strict fibre, not in W₁. The two triangles have consecutive edges (a,g),(g,a), and their long edges equal the appropriate identity components. The degree-two Segal map is a trivial fibration by Reedy fibrancy, so these triangles express exactly the inverse equations in hW. Requiring a common inverse representative is equivalent to the source's two inverse classes. |
| W_eq is the union of invertible components | `equivalenceArrows` | `Enhanced.fullSubcomplex` is applied to vertices whose π₀ class contains an equivalence arrow. All vertices of a simplex lie in the same component, so this is the whole union of components, with no missing higher simplices. |
| Complete Segal condition | `IsComplete` | Contains `IsSegal`; the factor s satisfies `s ≫ ι = W.map (σ 0).op` and is a weak equivalence. The subcomplex inclusion is mono, so this s is the unique actual degeneracy factor, not an arbitrary map. |
| I[m], its nerve E(m), and its cosimplicial structure | `equivalenceResolution` | `SimplexCategory.toCat ⋙ Cat.objects` gives Fin(m+1) and the actual monotone vertex maps; `uliftFunctor` changes only size. `Codiscrete.functorToCat` gives one arrow per ordered pair. `nerveFunctor ⋙ outerDiscrete` gives the ordinary nerve with inner operators identities. |
| F(n), cK and W^A | `outerRepresentable`, `innerConstant`, `powerResolution` | These precompose by the outer/inner projections as required. Mathlib's `MonoidalClosed.internalHom` on this functor category has `FunctorToTypes.rightAdj`/`Functor.functorHom`; its value is `HomObj A W` on the product-index coyoneda. `Functor.homObjEquiv` identifies this with maps A × F(n) × cΔ[q] → W, and its maps precompose in both representables. |
| Simultaneous resolution/inner diagonal | `resolutionDiagonalIndex`, `resolutionDiagonal`, `tilde` | Index object (n,q) goes to (q,(n,q)); an arrow (α,β) goes to (β,(α,β)). Thus exactly W̃_(n,q)=(W^E(q))_(n,q), with both β actions. |
| Collapse-induced map W → W̃ | `powerResolutionUnit`, `constantResolutionDiagonalIso`, `tildeUnit` | Curries the second projection E(m) × W → W. It is precomposition with the unique collapse to F(0); the constant-resolution identification and diagonal give the required natural map. |
| Chosen functorial Reedy replacement, levelwise weak equivalence | `R : ReedyReplacement.{u}` | Fields `functor`, `unit`, `fibrant`, `weak` are precisely this choice. The theorem quantifies over every choice; no normalization, objectwise equivalence witness, or auxiliary mapping-space assumption is added. The dependency model structure supplies functorial replacement; no data is extracted from a sorry-backed mere existence statement here. |
| W_hat and i_W | `completion R := tilde ⋙ R.functor`; `completionUnit R := tildeUnit ≫ whiskerLeft tilde R.unit` | Exact specified construction and composite, in the correct order. |
| W_hat is complete Segal | First conjunct of `rezk_explicit_completion` | `IsComplete ((completion R).obj W)` includes both completeness and the Segal/Reedy conditions. |
| Each induced mapping-space map is a weak equivalence | Second conjunct, `∀ x y : (row W ⦋0⦌) _⦋0⦌, ... (mappingSpaceMap ((completionUnit R).app W) x y)` | All source objects, and the actual comparison to the two image objects. No conclusion is assumed in R. |
| Every target object is isomorphic to an image object | Third conjunct `IsEssentiallySurjective ((completionUnit R).app W)` | For each target vertex z, gives x and an equivalence arrow with source i_W(x), target z. Equivalent to essential surjectivity of h(i_W). |
| Naturality in maps of Segal spaces | `completion R` is a functor; `completionUnit R` is a natural transformation on all spaces | Restriction to Segal spaces supplies exactly this clause. Not an omitted objectwise naturality claim. |

Edge cases: empty W and empty mapping fibres are admitted; no Nonempty binder
occurs. Terminal W and identity edges use actual degeneracies. Degrees 0 and 1
are not constrained by an extra Segal-map axiom, while Reedy fibrancy includes
degree zero. At m=0 the codiscrete groupoid has one object and the collapse is
the unique map to the terminal outer space. Ordinary category nerves with
noninvertible arrows are allowed, and noncomplete groupoid nerves are allowed
as inputs. Universe u is bound, arbitrary, and may be zero: the finite simplex
index has object and morphism universes zero, and ULift gives the same finite
object set in u. There are no ring, characteristic, scheme, or n>0 assumptions
hidden in this simplicial-homotopy statement. All variables are explicitly bound.

Dependency checks: I opened `EnhancedDiagramsCones.lean` (fullSubcomplex,
IsWeakHomotopyEquivalence), `KanQuillenRightProper.lean`
(right_proper_kan_quillen, including the horn-RLP fibration equality), and
`ReedyModelStructure.lean` (MatchingIndex, matchingProjection, matchingCone,
matchingFrom, model_structure). The matching category excludes exactly the
identity arrows and uses triangles in the negative wide subcategory. All three
interfaces are usable as recorded; no dependency repair/module is needed.
The six stated proof-dependency imports are ordinary imports; the others have
no recorded module. Reedy and Kan proof interfaces already enter through the
statement imports. The theorem docstring carries all eight node proof steps
and their cited dependencies; I compared them to the node. There is one named
postponed theorem and no sorry in any definition or structure data. Structural
naturality and functor-law proofs do not prove an additional theorem.

Independent H4 searches (new queries, recorded by msearch.py in searches.jsonl):

- LeanFinder: `A bisimplicial set has a functorial complete Segal space replacement inducing weak equivalences on fixed endpoint mapping fibers` returned eight ordinary nerve/strict-Segal and simplicial-nerve declarations, no completion theorem.
- Loogle: `"Segal", "fibrant"` returned zero hits.
- grep: `Reedy.*Segal|Segal.*Reedy|hoequiv|equivalenceResolution|rezk_explicit_completion` returned zero hits.
- LeanSearch: `Reedy fibrant bisimplicial sets with weak equivalence spine maps and invertible mapping component completeness` returned horn-fibration/model-category primitives and strict-Segal spine bijections, no Segal-space notion or completion statement.
- Independent local rg over Mathlib, upstream WeilConjectures, shared lean/Sheaf and dag/lean_names_upstream.json for `bisimplicial.*fibrant|complete.?segal|hoequiv|segalspace|reedy.*segal|segal.*reedy|rezk` found only an unrelated Rezk bibliography citation. I read Mathlib `SimplicialSet/Path.lean`, `PiZero.lean`, `NerveCodiscrete.lean`, `Functor/FunctorHom.lean`, and `Monoidal/Closed/FunctorToTypes.lean` to check the reused primitives and internal hom.

H12 new-node reading: `def-coef-segal-space` introduces the exact Section 2/4--6
notion just matched above, with essential surjectivity from 7.4. It is absent
from the base DAG and Lean library. The nearby DAG exponent, classifier,
categorical-equivalence and Rezk-model nodes are statements, not a competing
definition module; enriched algebroid/Segal-presheaf definitions concern a
different notion. The worker's blueprint search and upstream searches, plus my
fresh searches above, give no exact existing definition. The new node has the
specified definition fields, no proof, empty proof dependencies, null match,
three actual search kinds, matching chapter/unit, the item's ancestor and via
path, none audit states, and the complete declaration list. Its sole module
contains real constructions only; the item cites it in stmt_deps. There are no
sibling dependency modules to review under H13. No source-based statement
correction, citer modification, or mathematical weakening was necessary.
