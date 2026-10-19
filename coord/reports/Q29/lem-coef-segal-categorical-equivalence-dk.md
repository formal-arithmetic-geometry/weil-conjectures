## Worker report

Module: `Sheaf.AlgebraicTopology.SegalCategoricalEquivalence`, main declaration
`SSet.Segal.categorical_equivalence_dk`. The node's statement, dependencies and all
other pre-existing fields are unchanged; only `lean` is set. Nothing is proved:
the two named theorems have whole-body `sorry` proofs. All definition data are
explicit. No independent missing notion is needed: every helper renders a notion
already introduced in this item's own statement, and all helpers are listed in
`lean.declarations`.

Read the three dependencies, their full recorded statements and the signatures
and docstrings in the published local source. Also read the stage brief, stage-2
rules, delivery-errors H, CompactObject example and its node, setup, goal, state,
worker role and tools README. There was no repair note for this item.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Small simplicial sets and realization weak homotopy equivalences | `SSet.{u}` and the recorded `SSet.Enhanced.IsWeakHomotopyEquivalence`; no substitute weak-equivalence predicate. |
| Simplicial space `Δᵒᵖ → sSet` | `SSet.Segal.Space.{u}`. Outer direction is the first functor variable. |
| Reedy fibrant | `IsReedyFibrant V` requires the recorded `Reedy.matchingFrom` to be a Kan fibration in every outer degree. Negative maps of `Δᵒᵖ` are `(monomorphisms SimplexCategory).op`, namely opposites of injections. This is the fibrant-object matching test of the recorded Reedy model structure. |
| Consecutive-edge map to the iterated strict product | `spineSpace V n` uses Mathlib `SSet.Path` degreewise, including vertices, consecutive edges and their source/target equations; `segalMap` is Mathlib `SSet.spine` in every inner degree. For `n ≥ 2`, the vertex coordinates are determined by the arrows, so this is canonically exactly the stated iterated fiber product. |
| Segal condition for every `n ≥ 2` | `IsSegal V := IsReedyFibrant V ∧ ∀ n, 2 ≤ n → IsWeakHomotopyEquivalence (segalMap V n)`. |
| Vertices `x,y ∈ V₀` | `(V.obj (op ⦋0⦌)) _⦋0⦌`; no quotient of the object set. |
| Strict fiber of `(d₁,d₀)` | `mappingFiberSubcomplex` imposes both endpoint equalities on the entire inner simplex, using its constant simplex at `x` or `y`; `mappingFiber` is its actual underlying simplicial set. This is not merely a full subcomplex on endpoint vertices. |
| Homotopy category with those objects and hom sets `π₀ M_V(x,y)` | `homotopyCategory V := SSet.hoFunctor.obj (row V (op ⦋0⦌))`, the edge-path category modulo reflexivity and outer triangle relations. `object V x` names exactly the original vertex (Mathlib `hoFunctor.obj.equiv` is its object bijection). `fiberEdge` sends an arrow vertex to its generator. The named theorem `homotopyCategory_homs` states surjectivity of this map and equality exactly when the two vertices have equal Mathlib `SSet.π₀.mk` classes. Together these specify precisely the canonical bijection from `π₀ M_V(x,y)` to the hom set. This theorem formalizes the node's introductory hom-set clause, not an additional independent assumption. |
| Identity from `s₀` and composition from degree-two Segal map and `d₁` | Mathlib's free reflexive category makes the degenerate edge the identity; its homotopy-category quotient imposes `d₂(t) ≫ d₀(t) = d₁(t)` for every outer triangle. Hence any degree-two Segal lift computes exactly the category's composition. The hom-set identification theorem has a complete source-based proof docstring. The category data themselves use no unproved existence choice. |
| `V_eq` union of components representing isomorphisms | `equivalenceSubcomplex V` is the full subcomplex on vertices whose `SSet.π₀` component contains an `a` with `IsIso (edgeClass V a)`. Every simplex lies in one component, so this is precisely that union of components. |
| `F(n)_k = Hom_Δ([k],[n])`, discrete inner direction | `F n := discreteSpace Δ[n]`; `Δ[n]` is Mathlib's universe-lifted representable. `discreteSpace` composes with the constant-functor construction. |
| `I[1]` has objects zero and one, unique arrow per ordered pair | `WalkingIso := Codiscrete (ULift Bool)`. `false` is zero and `true` is one; universe lifting adds no objects. Mathlib's codiscrete category has singleton hom sets, so all arrows are invertible. |
| `E` is the ordinary nerve, discrete inner direction | `E := discreteSpace (CategoryTheory.nerve WalkingIso)`. |
| `e₀,e₁ : F(0) → E` | `endpoint false` and `endpoint true`, via the constant simplicial maps selecting the appropriate nerve vertices. |
| `a : F(1) → E` selects `0 → 1` | `intervalArrow`, using `SSet.yonedaEquiv.symm` on `ComposableArrows.mk₁` of that unique arrow. |
| Categorical homotopy `H : A × E → B` with two endpoint restrictions | `AreCategoricallyHomotopic f₀ f₁` quantifies over `H : A ⊗ E ⟶ B` and both displayed composition equalities. The Cartesian tensor is the degreewise product. `toFZero` and `cylinderEndpoint` construct its actual endpoint inclusions. |
| `U,V` Segal spaces | `hU : IsSegal U`, `hV : IsSegal V`. |
| Maps `f : U → V`, `g : V → U` | The explicit `f` and `g` binders. |
| `gf ∼ 1_U` and `fg ∼ 1_V` | `hgf : AreCategoricallyHomotopic (f ≫ g) (𝟙 U)` and `hfg : AreCategoricallyHomotopic (g ≫ f) (𝟙 V)`; Lean writes composition in traversal order. |
| All strict mapping-space maps are weak equivalences | First conclusion: `∀ x y, Enhanced.IsWeakHomotopyEquivalence (mappingFiberMap f x y)`. The induced map applies `f₁` in every inner degree, with the actual images under `f₀` as endpoints. |
| `hf : hU → hV` is an ordinary categorical equivalence | Second conclusion: `(homotopyFunctor f).IsEquivalence`. This is the functor induced by the same `f` on edge paths and triangle relations, not an unrelated equivalence. |
| Every object of `hV` is isomorphic to some `f(x)` | Final conclusion quantifies over every original vertex `y` and supplies a vertex `x` and `Nonempty (object V (f₀ x) ≅ object V y)`. No choice of such an object is made in a definition. |

Dependencies and source interfaces used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsWeakHomotopyEquivalence` and `SSet.Enhanced.fullSubcomplex`.
  The weak equivalences use geometric realization, path components and all
  positive based homotopy groups, as the node requires.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen` supplies the Kan model interpretation
  and right properness; its scoped Mathlib Kan-fibration structure is used in
  `IsReedyFibrant`. Its theorem is imported, not duplicated.
- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.matchingFrom`, `model_structure` and
  `simplex_reedy_structure`. The concrete matching construction and the opposite
  injection class define the required Reedy fibrancy without choosing a model
  structure witness.
- Mathlib `SSet.Path`, `SSet.spine`, `SSet.hoFunctor`,
  `SSet.Truncated.HomotopyCategory.mk` / `homMk`, `SSet.π₀` / `π₀.mk`,
  `CategoryTheory.nerve`, `Codiscrete`, the constant-functor construction and
  Cartesian products are reused directly.

The source PDF was opened online at the exact URL in the node. Read Sections 4,
5.1--5.8, 13.1, 13.3, Proposition 13.8 and Lemma 13.9. The common-inverse case
agrees with the source. The homotopy-category presentation retains the source's
objects and component hom sets; the named characterization theorem makes this
identification explicit, rather than silently substituting a different category.

Edge cases checked before writing: empty Segal spaces have no vertices, so the
mapping and object-surjectivity clauses are vacuous; a purported inverse from a
nonempty `V` to empty `U` cannot exist. The terminal Segal space has singleton
mapping spaces. Discrete ordinary nerves give ordinary natural isomorphisms and
categorical equivalences. A noninvertible arrow cannot become a categorical
interval endpoint homotopy, because `E` contains both inverse arrows and their
relations. Empty mapping fibers remain empty, and equality of objects is never
assumed for `x,y`. Degree zero Reedy fibrancy includes the empty matching index;
no Segal equivalence is imposed in degrees zero or one. Arbitrary universe `u`
is explicitly bound; the interval's two objects are lifted to that same universe.

Searches for existing declarations:

- `msearch.py ... leanfinder` with query "Categorical homotopy equivalences of
  Segal spaces induce weak equivalences on mapping spaces and equivalences on
  homotopy categories": eight hits, chiefly Mathlib's simplicial-set homotopy
  category and nerve adjunction. Read the former and reused its presentation;
  none states the Segal-space result.
- `msearch.py ... loogle '\"Segal\", \"equivalence\"'`: zero hits.
- `msearch.py ... grep 'SegalSpace|categoricalHomotopy|CategoricalHomotopy|Rezk'
  AlgebraicTopology`: zero hits.
- `msearch.py ... leansearch` with query "Segal space categorical homotopy
  equivalence is a Dwyer Kan equivalence": eight hits concerning ordinary model
  weak equivalences, strict Segal simplicial sets and simplicial enrichments;
  no matching theorem.
- `rg` in the pinned Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf`
  and upstream declaration index for `SegalSpace`, `IsSegal`, `segalMap`,
  `CategoricalHomotopy`, `categoricalHomotopy`, `WalkingIso`, `SSet.Segal`,
  `categorical_equivalence_dk` and `homotopyCategory_homs`: no existing Segal-space
  interface or matching names. Unrelated row constructions and mapping-fiber
  prose were inspected. The exact blueprint-id search in upstream had no match.

No disputed statement, dependency fault, new node or statement correction.

Validation: compile every delivered file through the prescribed `scompile.py`
wrapper. Final compile and dry-run results are recorded below once complete.

Final `scompile.py Q29 lem-coef-segal-categorical-equivalence-dk
lean/Sheaf/AlgebraicTopology/SegalCategoricalEquivalence.lean` passed both sandbox
and library-module checks, in 2.9 s and 2.8 s respectively, with no errors or
warnings. All 289 source lines meet the 100-character limit. Exactly two named
theorem proofs are postponed; no definition depends on either theorem.


## Second reading by Q29

Independent review against the actual node, every helper in
`Sheaf.AlgebraicTopology.SegalCategoricalEquivalence`, the three dependency nodes,
and their recorded source declarations. I did not write the worker module.
No repair note exists at `coord/repair-notes/lem-coef-segal-categorical-equivalence-dk.json`.
The node has no `statement_change`; this review found no reason to correct its
mathematical statement. There are no new nodes or dependency modules in this delivery.

I opened the exact Rezk PDF URL from the node, not a Stacks surrogate. Checked
Sections 2.1--2.4, Definition 4.1 and (4.2)--(4.3), Sections 5.1, 5.3--5.5 and
5.7, Sections 13.1 and 13.3, Proposition 13.8 and Lemma 13.9 (printed pages
5--7, 11--14, 29--32). The source assumes Reedy fibrant Segal spaces; it does not
assume completeness. The node's single common inverse is the stated special
case of the source's possibly different left and right inverse maps.

My object/hypothesis/conclusion checklist follows. Each verdict is about the
actual source signature and construction, not just the worker's report.

| Item introduced or asserted by the node | Lean rendering and verdict |
| --- | --- |
| Arbitrarily small simplicial sets and realization weak homotopy equivalences | `Space.{u}` takes values in `SSet.{u}`. `Enhanced.IsWeakHomotopyEquivalence` is exactly the dependency's bijection on realization components and every positive based homotopy group. PASS. |
| Simplicial space with outer index in the opposite simplex category | `Space := SimplexCategoryᵒᵖ ⥤ SSet.{u}`; `row V k` evaluates the inner direction, leaving the outer direction simplicial. PASS. |
| Reedy fibrancy for the standard opposite simplex Reedy structure | `IsReedyFibrant` tests `fibrations SSet` on every `Reedy.matchingFrom (monomorphisms SimplexCategory).op V k`. Opened the dependency's `MatchingIndex`, `matchingProjection`, `matchingCone`, `matchingFrom`, `rightClass`, `model_structure`, and `simplex_reedy_structure`. Its negative arrows here are exactly opposites of injections, with identities excluded in the matching category. No extra model-structure witness or assumption is added. PASS. |
| Consecutive-edge map into the iterated strict pullback | `spineSpace` uses Mathlib `SSet.Path` degreewise, and `segalMap` uses `SSet.spine`. Opened `Path₁`, its source/target equations and spine formulas: arrows are the consecutive edges. For positive length the vertex coordinates are uniquely determined by the arrows, so this is the same strict iterated pullback with redundant determined coordinates. PASS. |
| Segal weak equivalence in every degree at least two | `IsSegal V` is exactly Reedy fibrancy and `∀ n, 2 ≤ n → Enhanced.IsWeakHomotopyEquivalence (segalMap V n)`. PASS. |
| Vertices of the degree-zero space as objects | `x y : (V.obj (op ⦋0⦌)) _⦋0⦌`; `object V x` is Mathlib's `HomotopyCategory.mk x`. Opened `hoFunctor.obj.equiv` and `mk_surjective`: every object corresponds to precisely such a vertex. PASS. |
| Strict fiber of `(d₁,d₀)` over `(x,y)` | `mappingFiberSubcomplex` fixes both endpoint simplices to the degeneracies of `x,y` in every inner degree; `mappingFiber` takes its underlying simplicial set. This is the actual strict fiber, including higher simplices, with the stated source/target order. PASS. |
| Hom sets are components of that strict fiber | `fiberEdge` takes its vertex to the associated edge generator. `homotopyCategory_homs` requires surjectivity and equality iff `π₀.mk a = π₀.mk b`. Opened Mathlib's `π₀` (quotient by the equivalence relation generated by edges), `HoRel₂`, `HomotopyCategory`, and `homMk`. Together these give precisely the canonical bijection from fiber components to each hom set; the theorem assumes only `IsSegal V`. This renders the node's introductory hom-set clause. PASS. |
| Identity and composition have the specified source | Mathlib's free reflexive category makes the `s₀` edge the identity; `HoRel₂.of_compStruct` identifies two consecutive edges with `d₁` of their outer triangle. A degree-two Segal lift is exactly such a triangle. Thus the hom-set identification respects both operations, without chosen category data from an existence sorry. PASS. |
| Union of components of invertible edges | `equivalenceSubcomplex` uses the recorded `Enhanced.fullSubcomplex`, selecting vertices whose `π₀` class contains an edge with `IsIso (edgeClass V a)`. All vertices of a simplex have the same component, so this full subcomplex is exactly the required union. PASS. |
| Representables `F(n)` for all natural numbers, discrete inside | `F n := discreteSpace Δ[n]`. Opened the representable and constant-functor interfaces: outer operators are precomposition and inner operators are identities. The `ULift` of the finite hom set changes no mathematical elements. PASS. |
| Two-object groupoid with unique arrow for each ordered pair | `WalkingIso := Codiscrete (ULift Bool)` has precisely the objects false and true and singleton hom sets. `E` is its ordinary nerve through `discreteSpace`. PASS. |
| Endpoint maps and arrow `0 → 1` | `endpoint false`, `endpoint true` are the constant nerve maps; `intervalArrow` uses Yoneda on `ComposableArrows.mk₁` of the unique arrow from false to true. Endpoints and direction agree. PASS. |
| Homotopy between arbitrary maps of simplicial spaces | `AreCategoricallyHomotopic f₀ f₁` is existence of `H : A ⊗ E ⟶ B` with both endpoint equations. The Cartesian tensor is the degreewise product, and `cylinderEndpoint` pairs the identity with the indicated constant endpoint through `toFZero`. There is no accidental demand for equality of the maps. PASS. |
| Segal spaces `U,V` and maps in opposite directions | Main binders `hU : IsSegal U`, `hV : IsSegal V`, `f : U ⟶ V`, `g : V ⟶ U`, and no other hypotheses. PASS. |
| Both composites categorically homotopic to the identity | `hgf` uses `f ≫ g` on `U`, and `hfg` uses `g ≫ f` on `V`; traversal-order composition matches `gf`, `fg` in the node. PASS. |
| Weak equivalence on every specified mapping space | First conjunct quantifies over all original vertices `x,y` and uses `mappingFiberMap f x y`. Read its actual endpoint naturality equations: the map is induced by `f₁`, with endpoints `f₀ x,f₀ y`. PASS. |
| The induced functor on homotopy categories is an equivalence | `homotopyFunctor f` is `hoFunctor.map` of the actual inner-degree-zero evaluation of `f`. The second conjunct is its `IsEquivalence`, not an arbitrary equivalence or merely equality of object classes. PASS. |
| Every target object is isomorphic to an image object | Final conjunct is `∀ y, ∃ x, Nonempty (object V (f₀ x) ≅ object V y)`. The object bijection above makes vertex quantification exactly quantification over all objects; `Nonempty` asserts existence of an isomorphism without choosing data. PASS. |

Dependency review: `EnhancedDiagramsCones` defines the actual realization
predicate and full subcomplex used here; neither was copied. `KanQuillenRightProper`
uses the same realization predicate and Mathlib horn fibrations, rather than an
unrelated weak-equivalence structure. `ReedyModelStructure` supplies actual
matching limits and the simplex opposite Reedy structure. No ring, scheme,
Noetherian, characteristic, finiteness or inhabitation assumption is present.
All variables and the universe `u` are bound; no independent smaller test universe
makes a condition vacuous. Different small sizes can be compared in a common
larger universe, as the node's small-set convention allows.

Edge cases: empty `U,V` are permitted, and all vertexwise conditions are then
vacuous. A map from nonempty `V` to empty `U` cannot supply `g`, as expected.
Empty mapping fibers are actual empty simplicial sets; no basepoint is chosen.
The degree-zero matching category is empty and its limit terminal, so fibrancy
still asserts the Kan condition on `V₀`. The Segal condition begins at two,
without adding conditions at zero or one; `F(0)` and both endpoint maps are
present. The terminal Segal space has singleton mapping spaces. Discrete nerves
reduce the criterion to ordinary equivalence from inverse natural isomorphisms;
the invertible categorical interval does not accidentally encode a noninvertible
natural transformation. No characteristic or scheme-specific edge case applies.

Independent searches, with different words from the first reader:

- `msearch.py ... leanfinder "bisimplicial set Reedy fibrant Segal condition equivalence via invertible natural transformations"`: eight hits, all single-simplicial strict Segal/nerve/coskeletal facts. Read `StrictSegal` and the `Path` interfaces: bijective spine on sets is not this weak-equivalence condition on simplicial spaces.
- `msearch.py ... loogle '"Segal"'`: twelve hits for `SSet.IsStrictSegal`, `StrictSegal` and truncated variants. None is the notion or theorem here.
- `msearch.py ... grep 'bisimplicial|Rezk|Segal.space|Dwyer.?Kan' AlgebraicTopology`: no Mathlib hit.
- Direct `rg` on the pinned Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf` and `dag/lean_names_upstream.json` for `SegalSpace|segalSpace|IsSegal|namespace SSet.Segal|CategoricallyHomotopic|Rezk`, and for the actual declaration names: no existing matching interface. Broader hits concerning simplicial categories, coherent nerves, bisimplicial diagonal weak equivalences and composition spines were inspected as distinct notions. Reuse of Mathlib's path/triangle presentation and component quotient is appropriate; dropping this module as `existing` would not state the node.

Mismatch repaired: H8. The main theorem's proof docstring summarized an inverse
argument with two-out-of-three, which did not carry the node's four proof steps.
Replaced that paragraph with the actual currying formulas, endpoint identities,
the two triples `(kU,p₁,1_U)`, `(kV,p₁,1_V)`, the composition steps, and the final
triple `(f,g,f)`, naming all three recorded proof dependencies. This follows
Proposition 13.8 and Lemmas 13.9 and 7.5 and does not alter the theorem signature.
Those proof-dependency nodes currently have no Lean binding, so no unavailable
proof-module import was invented. No H3/H4/H5/H6 mismatch was found. Both postponed
theorems are clauses of this node and have source/blueprint and proof docstrings;
all definition data and structural naturality proofs are real. There is no
private declaration, local notation, local instance, hollow definition or new axiom.

Validation before preflight: the required `scompile.py` passed both sandbox and
library-module compilation, 1.9 s and 2.0 s, with no errors or warnings. Rechecking
after the docstring repair is recorded below. The JSON `lean.statement` was checked
verbatim against the full theorem signature; all non-`lean` node fields equal
the shared baseline. All Lean lines are at most 100 characters.

Post-repair validation: `scompile.py Q29 lem-coef-segal-categorical-equivalence-dk
lean/Sheaf/AlgebraicTopology/SegalCategoricalEquivalence.lean` passed the sandbox
and library-module compiles in 2.8 s and 3.0 s, with no warnings or errors.
`deliver2.py Q29 lem-coef-segal-categorical-equivalence-dk --no-push` printed
`OK (dry run): commit f021255b8e passes the preflight and compiles; nothing pushed`.
The tool handled worktree, delivery and shared-fetch contention itself.
