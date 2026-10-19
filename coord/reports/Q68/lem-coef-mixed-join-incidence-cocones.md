## Worker report

`Sheaf.CategoryTheory.MixedJoinIncidenceCocones` states
`SSet.Enhanced.mixed_join_incidence_cocones`. Its only postponed proof is this
one theorem. Four helper definitions in the same module specify its cylinder,
strict endpoint fiber, replacement assertion, and arbitrary-replacement triangle.
They contain real data or explicit predicates, with no choices from existence
statements and no postponed auxiliary theorem.

The statement matches the node as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small simplicial set K, small poset I | `K : SSet.{u}`, `I : Type u`, `[PartialOrder I]` |
| Monotone simplicial subsets K_i | `U : I → K.Subcomplex`, `hmono : Monotone U` |
| Mixed subset H | The existing `(localUnionCollage U).toSSet`, imported through the mixed-subset dependency |
| V_n consists of pairs with first-stage membership | The existing `(directedCoverIncidence U).toSSet`; the first conjunct identifies its all-vertices membership condition with membership at `z.2.obj 0` |
| Operators restrict the simplex and chain, increasing the first index | These are the inherited operators of `directedCoverIncidence`, a subcomplex of `K ⊗ nerve I`; first-stage equivalence is supplied for every degree |
| Projections u, v and constant-index maps v_i | The existing `directedCoverToShape U`, `directedCoverToIndex U`, and `directedCoverFiber U i` |
| Quasicategory E and arbitrary map q | `E : SSet.{u}`, `[Quasicategory E]`, `q : H ⟶ E` |
| p and c are the pure restrictions of q | `localUnionShape U ≫ q` and `localUnionIndex U ≫ q` |
| Use the specified join-slice comparison | `κ`, `hκ`, `cmp`, `hcmp` specify the existing collapse and comparison: `hκ` is exactly its degreewise cylinder equation, and `hcmp` is `IsJoinCoconeComparison κ p (cmp p)` for every shape and diagram into E |
| Canonical a₀, including its full two-block simplex formula | Existential `b`, predicate `IsMixedJoinIncidenceCylinder U b`, and `a₀ = b ≫ q`; that predicate fixes the composite into the ambient ordered join in every degree by `bluntSharpCylinderSimplex` |
| Pure blocks when the other block is empty | They are included by the existing `bluntSharpCylinderSimplex` selection formula, which selects an entire pure block for a constant interval simplex |
| Endpoints of a₀ | The equations `SSet.ι₀ ≫ a₀ = u ≫ p` and `SSet.ι₁ ≫ a₀ = v ≫ c` |
| Restriction of a₀ is exactly the associated local coherent cocone | For each i, the existential `s : (joinCocone (p|K_i)) _⦋0⦌` has `s.extension = localUnionCone U i ≫ q`; the displayed fiber equation is `v_i × id` followed by a₀ equal to `coconeHomotopy ... ((cmp ...).app _ s)` |
| Prescribed η_i with apex c(i) | The universal `η` and its apex equality inside `MixedJoinLocalReplacement` |
| Chosen equivalences in the strict apex fibers | The family `e` takes values in degree one of `calculusFiber (calculusApex ... false) c(i)`; its source is identified with the associated cocone by its entire `coconeHomotopy`, its target is exactly `η i`, and `IsEquivalenceEdge` is required in that strict fiber |
| Replacement a with exactly the same endpoints | Existential `a` in `MixedJoinLocalReplacement`, with both explicit endpoint equations |
| Every restriction of a is exactly η_i | The universal `directedCoverFiber` equation in `MixedJoinLocalReplacement` |
| Relative equivalence a₀ → a in the strict fixed-endpoint fiber | `h : (incidenceEndpointFiber a₀).toSSet _⦋1⦌`, its source/target equations in the ambient functor object, and `IsEquivalenceEdge (incidenceEndpointFiber a₀).toSSet h` |
| Restrictions are the chosen local equivalences, not just their homotopy classes | The final equality in `MixedJoinLocalReplacement` compares the restriction of the uncurried global edge to the double uncurry of `(e i).val.val.2`, with the associator specifying the product order |
| Every join cocone on q, with its actual apex | Universal `s : (joinCocone q) _⦋0⦌` in `MixedJoinIncidenceTriangles`; `s.extension` and `s.base` are its actual join map and apex |
| Associated λ and ν on p and c | Restrict the actual comparison image `(cmp q).app _ s` by the existing `gluingCoconeRestrict` maps for the pure shape and nerve inclusions |
| Triangle for any a and specified relative equivalence, not only the one constructed | `MixedJoinIncidenceTriangles` universally quantifies `a` and every edge `h` in the same strict endpoint fiber, with the exact source, target and equivalence conditions |
| The faces d₂, d₀, d₁ | The three equations using `stdSimplex.δ 2`, `stdSimplex.δ 0`, `stdSimplex.δ 1` give respectively a, the index pullback of ν, and the shape pullback of λ |
| No initiality, colimit, cover, directedness or nonemptiness assumption | None occurs among the hypotheses or the helper predicates |

The comparison binders are the explicit interpretation of “use ... the
join-slice comparison” in the node. They do not assume an arbitrary comparison:
the existing cylinder formula and `IsJoinCoconeComparison` determine its entire
coherent arrow, including all higher simplices, and its apex. The dependency
`join_slice_cocone_comparison` supplies such maps. Even when a shape is empty,
`IsJoinCoconeComparison` fixes its apex; no vacuous cylinder formula is used to
forget that apex.

`incidenceEndpointFiber` is the intersection of the two existing
`calculusFiber` constructions for restriction to times zero and one. This is
the degreewise strict fiber of restriction to `V × ∂Δ[1]`, since that boundary
is the disjoint union of the two endpoint vertices. Equivalence is asserted
inside this fiber, so the inverse triangles also fix both endpoint diagrams.
Likewise the chosen local equivalences are asserted inside their strict apex
fibers. The uncurrying equation has product order `(K_i × Δ[1]_t) × Δ[1]_s`
on both sides, using the associator on the double-uncurried local edge.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`,
  `diagramVertex`, `coconeCategory`; ordinary nerves, standard simplices,
  products and internal hom are the Mathlib constructions this module uses.
- `Sheaf.CategoryTheory.JoinSliceCoconeComparison`: `JoinCoconeSimplex`,
  `joinCocone`, `IsJoinCoconeComparison`, `bluntJoinCylinderIncl`, and the
  cylinder characterization in `join_slice_cocone_comparison`.
- `Sheaf.CategoryTheory.DirectedCoverMixedSubsetCells`: its mixed-subset
  theorem and the transitive definitions `localUnionCollage`, `localUnionShape`,
  `localUnionIndex`, and `localUnionCone` from
  `Sheaf.CategoryTheory.InfinityDirectedUnionLocalColimits`.
- `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`, publicly imported by the
  comparison dependency: `calculusFiber` and `calculusApex`.
- Existing canonical helpers are reused from
  `Sheaf.CategoryTheory.DirectedCoverColimitAssembly`:
  `directedCoverIncidence`, `directedCoverToShape`, `directedCoverToIndex`,
  `directedCoverFiber`. Their full source definitions were read both locally
  and with `scompile.py --source`.
- That module publicly imports `Sheaf.CategoryTheory.FinalIndexColimit`,
  whose `coconeHomotopy` definition extracts the actual coherent arrow.
  `gluingCoconeRestrict` is the existing map from
  `Sheaf.CategoryTheory.InfinityColimitGluing`, imported by the mixed-subset
  framework.
- Both remaining recorded proof dependencies are imported:
  `Sheaf.CategoryTheory.EquivalencePrismExtension` and
  `Sheaf.CategoryTheory.FixedBoundaryFunctorKan`.

Import/DAG issue found and handled: the incidence definitions already belong
to the landed downstream assembly module. The first dry run rejected an added
DAG edge to its theorem as cyclic. The final node therefore changes only
`lean`; it reuses those real definitions without relying on the assembly
theorem. There is no duplicate incidence construction. Under
`stages/2-statements.md` §3 rule 7, the assembly module's proof-only import of
this new module must be omitted because it would close an import cycle.
The existing real definitions are independently usable while the downstream
theorem remains postponed. No wait on a downstream theorem or new cyclic edge
is introduced.

Edge cases read against the construction: empty I, empty K, empty individual
K_i, the empty incidence source, a zero-dimensional simplex, constant chains,
and an empty E. If I is empty, V is empty and H is K, and all relative cylinder
conditions are empty. If K is empty, V is empty and the local cocone still
retains its apex through the existing comma construction. Empty K_i do not
lose their apex, despite their empty cylinder. With empty E, the given q
forces H empty and hence K and I empty. Constant interval simplices select the
pure blocks; constant index chains give the entire local coherent cocone.
These cases impose no added hypotheses.

Searches (all made through the prescribed wrapper or named read-only trees):

- LeanFinder query `incidence simplicial set mixed join coherent cocone
  replacement`: eight hits on horn cocones and ambient subcomplex/model
  constructions, none stating this mixed-join replacement theorem.
- Loogle query `simplicial incidence cocone join`: unknown identifier
  `simplicial`, no result. This failed query is not evidence of absence.
- Mathlib grep query `incidence|mixedJoin|localUnionCollage`: no matches.
- LeanSearch query `Incidence simplicial set of monotone subcomplexes,
  coherent transformations over a mixed join, replacement by equivalent local
  cocones relative endpoints`: eight hits on `Subcomplex.image_monotone`,
  ambient cofibrations, relative morphisms and `toSSetFunctor`; none matches.
- `rg` for `incidence|mixedJoin|localUnionCollage|directed_cover` in
  `WeilConjectures` and `lean/Sheaf` found the existing incidence helpers and
  the mixed-subset definitions, which were reused. The upstream tree has no
  occurrence of the target node ID.
- `rg` for the main declaration and all four helper names in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and the upstream name index found no collision.

Source checked online:
[HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf), printed pp.
248–250, and [Kerodon 01NX](https://kerodon.net/tag/01NX) and
[01P1](https://kerodon.net/tag/01P1). The construction follows the eight
agent-written proof steps already recorded in the node; the module docstring
includes every step. No statement correction or disputed assertion is needed.

Validation: the complete module compiled through `scompile.py`, separately as
sandbox and library, with no errors or warnings. No global build was run.

## Second reading by Q68

This is the worker's self-check; the dispatcher brief forbids spawning another
agent and assigns independent review to the maintainer. I reopened the node
and the final module and matched every clause in the table above.

The review corrected three substantive omissions from the initial draft:
a₀ is now fixed on every simplex by the two-block formula; the global relative
equivalence retains the actual chosen local edges; and the triangle assertion
is universal in both the replacement a and its relative equivalence. It also
uses equivalence in the actual strict fibers, rather than merely equivalence
in the ambient functor simplicial set, and preserves the independent existence
of a₀ before local cocones are prescribed.

I checked source/target orientation: `δ 1` is the source of an edge and `δ 0`
is its target; triangle faces `δ 2`, `δ 0`, `δ 1` are 01, 12, 02. The
associator sends `(K_i × time_t) × time_s` to
`K_i × (time_t × time_s)` for the local-edge equality. Both endpoint maps and
the local cocone apices are fixed in every simplicial degree. The strict fiber
records inverse triangles relative to that same boundary. The final universal
triangle uses actual join cocones and their comparison images, rather than
arbitrary coherent cocones. The small poset remains arbitrary; no directedness,
cover, initiality, colimit or nonemptiness restriction was introduced.
