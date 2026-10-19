## Worker report

The delivery states `SSet.Enhanced.mapping_composition` in
`Sheaf.CategoryTheory.InfinityMappingComposition`. The sole postponed theorem is this
item, with `by sorry`; no other DAG node is restated. All helper definitions have real
data. The node copy was regenerated from the shared node and changes only `lean`.
No statement correction, dependency module, or new node is needed.

The earlier attempt was substantively incomplete. I replaced its unconstrained `J` by
an existential family fixed degree by degree by the recorded pinch-prism formula; fixed
both triangle restrictions (the old long-edge map was arbitrary); moved the composition
homotopy into `U(a,d)` itself; replaced vacuous associativity between unnamed maps by the
two actual bracketings; and added degenerate identities on components, the triangle
composition rule, edge representatives, and invertibility of component classes. I removed
the duplicate component quotient and homotopy definitions and use Mathlib `π₀` and
`Homotopy`. I removed the earlier author's claimed independent second reading: a fresh
second reader must supply that section.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small quasicategory in a fixed universe | `D : SSet.{u}`, explicit `universe u`, `[Quasicategory D]`; all objects use this same arbitrary universe. |
| Right-pinched mapping spaces `M(a,b)` | The dependency's `mappingSpace D a b`, unchanged. |
| Specified comparison `j : M → U` | The first existential in `MappingCompositionStatement`, with exactly the dependency's degreewise equation using `rightPinchPrism`, `uncurry`, `yonedaEquiv`, and `arrowMappingSpaceInclusion`. It fixes the entire simplicial map, not just its vertices. The dependency proves this particular map is a homotopy equivalence. |
| `V(a,b,d)` with all vertex factors constant | `triangleEndpointMap` evaluates at vertices 0, 1, 2; `triangleFiber` is its pullback against the constant vertex `(a,b,d)` from `Δ[0]`. Thus endpoints are fixed as entire simplices. |
| `θ` restricts to edges 12 and 01, in that order | `triangleEdgePair` uses `stdSimplex.δ 0`, then `stdSimplex.δ 2`; its equality with `θ` followed by both inclusions specifies `θ`. |
| `ℓ` restricts to 02 | `triangleLongEdge` uses `stdSimplex.δ 1`; the equation `ℓ ≫ arrowMappingSpaceInclusion = triangleLongEdge` specifies `ℓ`. |
| `V` is Kan and `θ` a homotopy equivalence | `KanComplex (triangleFiber ...)` and an actual inverse `r` with `Nonempty (Homotopy (θ ≫ r) (𝟙 _))` and `Nonempty (Homotopy (r ≫ θ) (𝟙 _))`. |
| Simplicial homotopy means a cylinder with endpoints | Mathlib `SSet.Homotopy f g` has `h : A ⊗ Δ[1] ⟶ B` with the endpoint equations; `Nonempty` asserts existence. |
| Canonical composition and its characterization | `c a b d : M(b,d) ⊗ M(a,b) ⟶ M(a,d)` and `Homotopy (c a b d ≫ j a d) ((j b d ⊗ₘ j a b) ≫ r ≫ ℓ)`. This is precisely `[j]c=[ℓ][θ]⁻¹([j]×[j])`, in categorical composition order. Uniqueness of the class follows by canceling the specified homotopy equivalence `j`; no arbitrary map is substituted for it. |
| Associativity on three inputs | The explicit homotopy between `(𝟙 ⊗ₘ c a b d) ≫ c a d e` and `α_.inv ≫ (c b d e ⊗ₘ 𝟙) ≫ c a b e`, on the right-associated triple product. |
| Both identity laws | The two homotopies using `lift (𝟙 _) (const i)` and `lift (const k) (𝟙 _)`, with `i.1 = D.σ 0 a`, `k.1 = D.σ 0 b`. Identity vertices actually exist by the component-category identity field, so these premises are not vacuous. |
| Ordinary category on vertices and `π₀ M(a,b)` | `ComponentCategoryData` has identity and composition on exactly these hom sets, both unit axioms and associativity, and `comp_on_vertices` identifies composition with `c`. These are the complete category data and laws, presented as a record rather than selecting a category instance. |
| Identities represented by degenerate edges | `id_on_vertices` supplies an identity mapping vertex over `D.σ 0 a` and identifies its `π₀.mk` with `H.id a`. |
| Every component represented by an edge | For each `x : π₀ (mappingSpace D a b)` the package supplies `u` with `π₀.mk u = x`. A mapping-space vertex is exactly a simplex of `D` in degree 1 with endpoints `a,b`. |
| Triangle gives `[v][u]=[w]` | The clause quantified over `t : D _⦋2⦌`, mapping vertices `u,v,w`, and equations `δ 2 t = u.1`, `δ 0 t = v.1`, `δ 1 t = w.1` concludes `H.comp ... (π₀.mk v) (π₀.mk u) = π₀.mk w`. |
| Invertible component iff the two inverse triangles exist | Existence of a component `v` satisfying both equations with `H.id` is equivalent to the dependency's `IsEquivalenceEdge D u.1`. Its definition is exactly the existential inverse edge and two 2-simplices with the six boundary equations in the node; it is used directly, rather than restating a tautological iff. |
| Pre/postcomposition are restrictions to an edge vertex | The final clauses use precisely `lift (𝟙 _) (const u) ≫ c` and `lift (const v) (𝟙 _) ≫ c`. |
| Depend only on component class | Equality of `π₀.mk u` and `π₀.mk u'` (respectively `v,v'`) implies a cylinder homotopy between those actual restricted maps. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `evaluation`, `IsEquivalenceEdge`, with their full source definitions/docstrings;
  the imported Mathlib `SSet`, `Quasicategory`, standard simplices and cartesian monoidal
  internal hom give the common models.
- `Sheaf.CategoryTheory.RightPinchComparison`: `arrowMappingSpace`,
  `arrowMappingSpaceInclusion`, `rightPinchPrism`, and the complete signature/docstring of
  `right_pinch_comparison`. Its existential comparison is uniquely specified by the prism
  formula; the delivery repeats that characterization within its conclusion instead of
  choosing arbitrary data from existence.
- The stated proof dependency `Sheaf.CategoryTheory.KanMappingHomotopyInvariance` is
  imported without `public`; its `kan_mapping_homotopy_invariance` signature/docstring were
  read. The Mathlib proof leaf `SSet.relativeCellComplexOfMono` is imported from
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` without `public`.
- `lem-cbc-simplicial-composition-spine` and `lem-coef-kan-realization-serre` have no Lean
  records in the read snapshot and are proof dependencies only, so there are no modules to
  import for them. Both statement dependencies are present and usable; nothing waits on an
  unstated statement prerequisite.
- Mathlib `SSet.Homotopy`, `SSet.π₀`, `SSet.π₀.mk` are used directly. The PiZero source
  defines components as vertices modulo the edge-generated equivalence relation.

Edge cases checked before rewriting: an empty quasicategory (all vertex-indexed conditions
are vacuous); empty individual mapping spaces and triangle fibers (Kan has no nonemptiness
condition and inverse maps are between the corresponding empty spaces); the point;
repeated vertices and degenerate edges; ordinary-category nerves, where mapping complexes
are discrete and composition is strict; the nerve of `[1]`, where its nonidentity edge is
not invertible; and groupoid nerves, where inverse triangles do exist. No condition on
characteristic, connectedness, nonemptiness, finiteness, or different universes is imposed.
The explicit associator accounts for the product bracketing without changing the input order.

Sources read online: [Kerodon 01PF](https://kerodon.net/tag/01PF), especially Corollaries
the project server/8, Construction the project server, Remark the project server, Propositions the project server/12, Remark
the project server and Notation the project server; [Kerodon 004Q](https://kerodon.net/tag/004Q), Definition
the project server and Remarks the project server/8. WANTED: archived copies of these Kerodon source pages in
literature; no literature files were modified.

Searches repeated with the prescribed `msearch.py Q46 lem-coef-infinity-mapping-composition`:

- LeanFinder: `Mapping space composition in a quasicategory is associative and unital up to
  homotopy with homotopy category components`. Returned `Truncated.Edge.CompStruct.*`,
  `Truncated.HomotopyCategory₂.instCategoryStruct`, and `QCat.bicategory`; none is composition
  on the specified full-dimensional right-pinched complexes.
- Loogle: `"Quasicategory", "comp"`. Returned only `SSet.instQuasicategoryOfKanComplex`.
- grep: `homotopy.*composition|composition.*homotopy|mappingSpace` in
  `AlgebraicTopology/Quasicategory`. One hit, `TwoTruncated.lean:216`, which only composes
  component morphisms. I read that declaration and `StrictBicategory.lean`: the latter
  composes functors between quasicategories, not morphisms within one.
- LeanSearch: `Composition on the Kan mapping spaces of an infinity category is associative
  and unital up to homotopy`. Returned `BifibrantObject.homMk_homMk_assoc`,
  `CofibrantObject.homMk_homMk_assoc`, `SimplicialCategory.sHomComp`, and unrelated results.
  These assume other categories or an existing enrichment, and do not provide this theorem.
- `rg` for `mapping_composition|MappingCompositionStatement|triangleFiber|SimplicialHomotopic`
  in both the project `lean/Sheaf` and upstream `WeilConjectures` returned no hits.
  `grep -rn` for the item id in upstream `WeilConjectures` returned no hits.
- A targeted Mathlib/project search for homotopy equivalence and component APIs located
  `Homotopy.lean` and `PiZero.lean`; their definitions replaced the draft's duplicate notions.

Validation: `scompile.py Q46 lem-coef-infinity-mapping-composition` compiled the delivered
module cleanly, including its newly published proof import in the private overlay. There
are no overlong Lean lines or automatically bound variables. Only this item's theorem uses
`sorry`; no disputed statement or node fault remains.

## Second reading by Q46

I did not write this statement. I read the current node, its five proof steps, the
sandbox module, both statement-dependency node records and their recorded source
modules. I also read the stated proof import `KanMappingHomotopyInvariance` and the
Mathlib definitions of `Homotopy`, `π₀`, `Quasicategory`, and `KanComplex`. There is
no repair note for this item, no `statement_change`, no new definition node, and no
dependency module in this delivery. Comparing the sandbox node with the shared
node shows that only `lean` changes.

The following is my object/hypothesis/conclusion checklist, made from the node
before checking the implementation. Every row passes.

| Node object, hypothesis, or clause | Lean rendering and verdict |
| --- | --- |
| A small quasicategory in one fixed sufficiently large universe | `universe u`, `(D : SSet.{u}) [Quasicategory D]`. The universe is arbitrary; there is no additional instance, nonemptiness, size equality, or finiteness hypothesis. Pass. |
| Vertices and the specified right-pinched spaces `M(a,b)` | Vertices have type `D _⦋0⦌`; `mappingSpace D a b` is imported from `EnhancedDiagramsCones`. I checked its degree-n subtype: the entire initial face is constant at `a`, the last vertex is `b`, and operators use `appendLast`. At degree zero these are exactly edges with source `a` and target `b`. Pass. |
| The specified comparison `j : M(a,b) → U(a,b)` | The existential `j` is constrained in every degree by the exact `rightPinchPrism` equation in `right_pinch_comparison`, after `arrowMappingSpaceInclusion`. I read that dependency's full signature, not just its name. The inclusion is the pullback inclusion fixing both endpoint simplices, hence is monic; the formula determines `j` uniquely. Its homotopy-equivalence property and both Kan properties follow from that dependency for this very map. No arbitrary comparison is substituted. Pass. |
| Cylinder homotopy with both endpoints | `Nonempty (SSet.Homotopy f g)` uses Mathlib's cylinder `A ⊗ Δ[1]` and endpoint equations `h₀`, `h₁`. No duplicate homotopy relation is introduced. Pass. |
| `V(a,b,d)` fixes all three vertex factors in every degree | `triangleEndpointMap` is evaluation at vertices 0, 1, 2; `triangleVertices` is `(a,b,d)` with matching right-associated product; `triangleFiber` is the pullback along the constant map from `Δ[0]`. This fixes whole simplices on the three factors. Pass. |
| `θ` is restriction to `12,01`, in this order | `triangleEdgePair` uses `stdSimplex.δ 0` and `stdSimplex.δ 2` in that order. The equation for `θ` after the product of the arrow inclusions fixes the actual map into `U(b,d) ⊗ U(a,b)`. Pass. |
| `ℓ` is restriction to `02` | `triangleLongEdge` uses `stdSimplex.δ 1`; the equation for `ℓ` after its arrow inclusion fixes this restriction. Pass. |
| `V` is Kan | `KanComplex (triangleFiber D a b d)` for every triple. Pass. |
| `θ` is a homotopy equivalence | An actual reverse map `r` and homotopies `θ ≫ r ~ 𝟙 V`, `r ≫ θ ~ 𝟙 (U(b,d) ⊗ U(a,b))`. Both equations have the correct source. Pass. |
| Composition on the right-pinched spaces with the displayed characterization | `c a b d : mappingSpace D b d ⊗ mappingSpace D a b ⟶ mappingSpace D a d`; the characterization is a homotopy in `U(a,d)` from `c ≫ j` to `(j ⊗ₘ j) ≫ r ≫ ℓ`. The inverse and restriction equations make this exactly the node's formula on classes; cancellation of the dependency's specified equivalence `j` gives uniqueness of the class. Pass. |
| Associativity for four vertices | The two maps are `(𝟙 ⊗ₘ c a b d) ≫ c a d e` and `α_.inv ≫ (c b d e ⊗ₘ 𝟙) ≫ c a b e`, on `M(d,e) ⊗ (M(b,d) ⊗ M(a,b))`. The associator changes brackets only, preserving the input order. Pass. |
| Both identity laws at degenerate edges | The identity restrictions are `lift (𝟙 _) (const i) ≫ c a a b` and `lift (const k) (𝟙 _) ≫ c a b b`, with `i.1 = D.σ 0 a`, `k.1 = D.σ 0 b`, each homotopic to the identity. `ComponentCategoryData.id_on_vertices` supplies such vertices, so the jointly quantified premises do not make either law vacuous. Pass. |
| An ordinary category with vertices as objects and `π₀ M(a,b)` as morphisms | `ComponentCategoryData D c` supplies precisely identities, composition, both unit laws and associativity on those hom sets. Its `comp_on_vertices` identifies composition with the degree-zero action of `c`; surjectivity of `π₀.mk` determines composition on all components. This is complete category data, without a choice from an unproved existence theorem. Pass. |
| Identity classes are represented by degenerate edges | `id_on_vertices` gives `i.1 = D.σ 0 a` and `id a = π₀.mk i`. Pass. |
| Every component has an edge representative | For every `x : π₀ (mappingSpace D a b)`, the package gives a mapping vertex `u` with `π₀.mk u = x`. Such a vertex is an actual endpoint-fixed edge by the dependency definition. Pass. |
| A triangle gives `[v][u] = [w]` | The quantified simplex `t : D _⦋2⦌` has equations `D.δ 2 t = u.1`, `D.δ 0 t = v.1`, `D.δ 1 t = w.1`; its conclusion is `H.comp a b d (π₀.mk v) (π₀.mk u) = π₀.mk w`. Pass. |
| Invertibility iff one inverse edge has both inverse triangles | The left side quantifies one inverse component and imposes both inverse equations. The right side is the recorded `IsEquivalenceEdge D u.1`. I unfolded its definition: it quantifies one edge `g` and two 2-simplices with the six required boundary equations, with long edges the two appropriate degeneracies. This is the claimed equivalence, not a mere restatement of invertibility. Pass. |
| Pre/postcomposition are restrictions of the canonical class and depend only on the edge component | The final clauses compare the actual maps `lift (𝟙 _) (const u) ≫ c` and `lift (const v) (𝟙 _) ≫ c` for vertices with equal `π₀.mk`, via cylinder homotopies. Both variables, sources, and component equalities match the node. Pass. |

Source check: I opened [Kerodon 01PF](https://kerodon.net/tag/01PF), including
the project server/8--12 and 14--15, and [004Q](https://kerodon.net/tag/004Q), especially
the project server/6/8. They require an infinity category and the named vertices, with no
additional ambient hypothesis. The former supplies fixed-vertex fibers, composition,
units, associativity, and component/pre/postcomposition behavior; the latter supplies
the inverse-triangle criterion. [01L5](https://kerodon.net/tag/01L5) confirms the
pinch equivalence used to transport the arrow-space formulation. These are Kerodon
sources, not Stacks tags. WANTED: archived copies of these pages under literature.

Edge cases: the empty quasicategory gives vacuous vertex-indexed assertions and the
empty category data. Individual mapping spaces can be empty; Kan does not require
vertices, and the triangle inverse has the corresponding empty source/target. The
point, repeated vertices, and all degenerate identity edges are included. On ordinary
category nerves the complexes are discrete and the formulas reduce to composition;
on `N([1])` the nonidentity arrow fails the invertibility clause, while groupoid nerves
have both inverse triangles. Degree zero is checked explicitly in the subtype and
triangle equations. There is no arithmetic, characteristic, scheme, or index-set
parameter, and the arbitrary common universe excludes none of the node's small cases.

Independent H4 searches, using different terms from the worker's first query:

- `msearch.py ... leanfinder "Composition of full right mapping complexes of a
  quasi-category through a fixed endpoint two-simplex fiber is associative up to
  cylinder homotopy"`: triangle-horn restriction lemmas and truncated left/right
  homotopy transitivity, not this statement.
- `msearch.py ... loogle '"Quasicategory", "Homotopy"'`: zero hits.
- `msearch.py ... grep 'Segal|fixed.*vert|sHomComp|HomotopyCategory₂'
  AlgebraicTopology/Quasicategory`: strict-Segal and 2-truncated category results.
  I read `TwoTruncated.lean`'s `Hom`, category structure and composition-witness API;
  these use a different edge quotient and do not construct the specified full mapping
  complexes or their composition class.
- `msearch.py ... leansearch "The triangle fiber of the internal functor simplicial
  set of a quasicategory gives associative and unital composition maps on right
  pinched Kan mapping spaces"`: `SimplicialCategory.sHomComp`, horn/composition
  witness declarations, and unrelated maps. I read `sHomComp`: it requires an
  already supplied simplicial enrichment, not constructed here.
- Direct `rg` for multiarrow, triangle-fiber, Segal, homotopy-category and mapping-space
  composition terms in upstream `WeilConjectures` and project `lean/Sheaf` found
  no equivalent declaration. I read `StrictBicategory.lean`: its objects are whole
  quasicategories and its 1-morphisms are functors. The exact names of all eight
  delivered declarations have no collisions in Mathlib, upstream, the project, or
  `dag/lean_names_upstream.json`. No existing binding should replace this module.

H5--H9: all helper definitions have explicit data; the category package is a structure,
not a chosen object. The only postponed theorem is `mapping_composition`, with `sorry`.
Every declaration has its source/blueprint docstring. The theorem's docstring follows
all five proof steps, including the section/cylinder lifting, conjugation by the pinch
comparison, cancellation for associativity and units, component cylinders, and the inner
3-horn producing inverse triangles. Statement dependencies are public imports; the two
available proof-only modules are ordinary imports. The other proof dependencies have
no Lean binding in the current node records. No line exceeds 100 characters, and all
variables and the single universe are explicitly bound.

Mismatches found and changes: none. I left the Lean module and node copy unchanged and
added only this independent second-reading section. `lean.statement` is verbatim equal
to the theorem signature in the file. Validation: the required `scompile.py Q46
lem-coef-infinity-mapping-composition
lean/Sheaf/CategoryTheory/InfinityMappingComposition.lean` succeeded for both the sandbox
check and the library-path compile, with no errors or warnings.
