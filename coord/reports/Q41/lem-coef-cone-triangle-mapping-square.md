# Q41: lem-coef-cone-triangle-mapping-square

## Worker report

This repairs the stage-2 return at immutable head 12c22c2a3287. The retained
sandbox had only launcher brief markers, no node copy, report, or Lean module.
The current base node likewise has no lean record. I read the return and the
current node, including its five proof steps, and supplied the missing stage-2
module rather than repeating the stage-1 split. Only the node's lean field changes.
No statement, dependency, proof, source, blueprint field, or target changes.

The module is lean/Sheaf/AlgebraicTopology/ConeTriangleMappingSquare.lean.
The principal declaration is SSet.ConeTriangle.cone_triangle_mapping_square.
Its only postponed theorem is that declaration, with proof `by sorry`. Every
definition has its full data; the declaration docstring reproduces all five proof
steps and names their dependencies. All thirteen declarations belong to this node
and are listed in lean.declarations. No new nodes or dependency repairs are needed.

Source read: the online IAS HTT PDF, Section 1.1.5, Notation 3.2.1.1 and Definition
3.2.1.2 (printed pp.170--171), and Proposition 3.2.1.11(4) (printed pp.175--176).
The first square there is the identity-long-edge case of the node's subset-cube
square. The current blueprint ancestor proof was also read: paragraph 2 of
prop-coef-integral-exceptional-adjoint, before the derived inverse limit, is the
reported origin for this technical foundation. The node already records the
expanded arbitrary-triangle argument; that argument and its route are retained.

Hypothesis and clause correspondence:

| Node clause | Lean rendering and check |
| --- | --- |
| Small simplicial sets, subset-poset coherent realization | `K : SSet.{u}` and `C : CategoryTheory.CoherentNerveComparisonStatement.{u}`. This is the dependency's recorded realization package, including its precise simplex objects, simplex maps and colimit extension. It is not an arbitrary simplicial category or a Kan replacement. The dependency theorem supplies such a package; the binder selects the stipulated realization, not a further condition on K. |
| Ordered right cone and new vertex v | `Enhanced.rightJoinCone K`, `base C K := C.rigidification.map (Enhanced.rightJoinConeInclusion K)`, and `point C K`, the pure final-factor vertex. No identification with an old vertex is imposed. |
| P and X_x=P(x,v) | `value C x := hom (C.rigidification.obj (Enhanced.rightJoinCone K)) ((base C K).obj (vertex C x)) (point C K)`. This is a mapping set in P itself, not an equivalent Kan model or a pushout with an unspecified comparison. |
| Cone arrow tilde-x | `D.coneArrow x`, normalized in `coneArrow_eq` by the full subset `{0,1}` in the coherent cone on x. |
| Edge e:x→y and its coherent-realization vertex | Mathlib `e : SSet.Edge x y`; `D.baseEdge e` is fixed by `baseEdge_eq` as the image of the unique full-subset vertex in the coherent realization of e. |
| e-star precomposition | `precompose C (D.baseEdge e)`. The full diagonal action is `action C x y`, obtained from the actual map of the old realization and `eComp`; `precompose` fixes the acting coordinate by `SSet.const`. |
| Coning edge tilde-e | `D.coningEdge e : Edge (D.coneArrow x) ((action C x y).app _ (D.baseEdge e, D.coneArrow y))`. `coningEdge_eq` fixes its entire raw edge as the image of `{0,2}⊆{0,1,2}` under the coned edge simplex. |
| Marking exactly degeneracies and g-star tilde-d for degenerate d | `markedValue D x` uses the recorded `SSet.Marked`. Its marking is the disjunction of `Set.range ((value C x).σ 0)` and exactly the stated generators. The generator quantifies over `d : Edge y z` with `d.edge ∈ Set.range (K.σ 0)` and every degree-one `g` in the old mapping set from x to y. It applies `action` diagonally to `(g,(D.coningEdge d).edge)`. Nothing closes the marking under composition. |
| Every triangle σ with faces e,f,k | `σ : e.CompStruct f k` in Mathlib. Its `simplex` has precisely these three raw faces, with the node's orientation. There is no restriction to nondegenerate triangles. |
| rho from k to the coherent composite fe | `D.coherenceEdge e f k σ` is an `Edge` from `D.baseEdge k` to `eComp` of `D.baseEdge e` and `D.baseEdge f`, in that order. `coherenceEdge_eq` normalizes its whole two-element subset chain in the image of `σ.simplex`. |
| A simplicial square H | The conclusion quantifies `∃ H : Δ[1] ⊗ Δ[1] ⟶ value C x`. The tensor here is the Cartesian product of simplicial sets. |
| Vertices (00),(10),(01),(11) | The first four conjuncts of `IsSquare` are respectively `D.coneArrow x`, `e* D.coneArrow y`, `k* D.coneArrow z`, and `e*(f*D.coneArrow z)`, evaluated at those ordered pairs. |
| Edges at second coordinate 0 and 1 | The next two conjuncts of `IsSquare` restrict along `(id,const 0)` and `(id,const 1)`. They equal the Yoneda maps of tilde-e and the diagonal action of `rho.edge` on the degenerate edge at tilde-z. This last formula is precisely rho-star tilde-z. |
| Edges at first coordinate 0 and 1 | The final two conjuncts restrict along `(const 0,id)` and `(const 1,id)`. They equal tilde-k and the image of tilde-f under e-precomposition. These are equalities of simplicial edge maps, not just equalities of endpoints. |
| rho-star tilde-z is marked | The second conjunct after `IsSquare` asserts membership of this exact raw edge in `(markedValue D x).marking`. |
| If k is degenerate, tilde-k is marked | The following implication has antecedent `k.edge ∈ Set.range (K.σ 0)` and conclusion `(D.coningEdge k).edge ∈ (markedValue D x).marking`. |
| Every old mapping vertex preserves E | The first conclusion, before the triangle quantifier, ranges over all w,x and every degree-zero `a` in the old mapping set, and all marked edges t. Its conclusion is marking membership of `(precompose C a).app _ t`. |
| It carries this square to the square with all four precomposed edges | For the same H, the last conclusion asserts `IsPrecomposedSquare D a e f k σ H` for every w and a. That predicate explicitly gives all four boundary equations for the actual composite `H ≫ precompose C a`, with precomposition applied to the corresponding computed edge. |
| Degenerate σ allowed; no Kan assumption | The only binders are the stipulated realization, arbitrary K, vertices, edges and a CompStruct. No `KanComplex`, `Quasicategory`, injectivity, nondegeneracy, connectedness or nonemptiness instance is requested. |

The canonical normalization is substantive, not an arbitrary-map assumption.
For each of its degree-zero test spaces there is the vertex of the path with
underlying subset `{0,1}`. For each degree-one test space there is the nerve edge
from the path `{0,2}` to the path `{0,1,2}`, induced by inclusion. These are actual
nonempty finite posets. Specifying their vertex subsets determines their entire
nerve simplices because the path category is a poset. Thus the four `_eq` fields
uniquely specify all raw arrow and edge data. `HEq` accounts only for the canonical
object-endpoint transports between their coherent-simplex images and the old/cone
vertex types. The theorem asserts existence of these normalized data, rather than
assuming arbitrary maps or constructing data from a bare existence claim.

Dependency declarations used, after reading their signatures and docstrings:

- Sheaf.CategoryTheory.CoherentNerveComparison:
  `CategoryTheory.CoherentNerveComparisonStatement`, especially `rigidification`,
  `simplex_realization`, `simplex_maps`, `colimit_extension`; the recorded
  `CategoryTheory.coherent_nerve_comparison` provides its nonempty existence.
  The module also supplies the existing `CoherentNerve.hom` and SCat interface.
- Sheaf.CategoryTheory.RelativeInfinityCone:
  `SSet.Enhanced.rightJoinCone`, `rightJoinConeInclusion`, and their existing
  ordered-join infrastructure (`orderedJoinInr`, `orderedJoinFunctor`,
  `joinPointTopSimplex`). The unrelated relative-colimit predicate is not copied.
- Sheaf.AlgebraicTopology.MarkedPointCartesianModel:
  `SSet.Marked` with its underlying object, marking set and degeneracy condition.
  No model-structure or fibrancy hypothesis is substituted for a marking.
- Mathlib.AlgebraicTopology.SimplicialNerve:
  `SimplicialThickening.Path`, its inclusion category, nerve enrichment and
  `eComp`. Mathlib.AlgebraicTopology.SimplicialSet.CompStruct:
  `SSet.Edge`, `SSet.Edge.CompStruct` and `CompStruct.simplex`.

The three proof dependencies are also exactly the three statement dependencies;
they are all imported. No proof dependency import is omitted.

Edge cases checked before writing and again while rereading:

- Empty K: no vertex-, edge-, marking- or triangle-indexed data are demanded.
  The new cone point is still defined from the pure final factor.
- K=Delta[0], and triangles s0/s1 of a single edge: repeated vertex labels are
  allowed by Edge/CompStruct. Direct image under `[2]→[1]`, 0,1↦0 and 2↦1,
  sends both interval subsets to `{0,1}`, so the coned degenerate edge is a
  degeneracy; the top marked edge remains the d=s0(z) generator.
- A nondegenerate Delta[2]: the four cube corners are `{0,3}`, `{0,1,3}`,
  `{0,2,3}`, `{0,1,2,3}` in the required order. Bottom and left are the e/k
  coning intervals. Right adds 2 after 1 and is e-star tilde-f; top adds 1
  before 2 and is rho-star tilde-z. This checks the two coordinate directions.
- Arbitrary non-Kan K and non-Kan coherent mapping simplicial sets: all
  constructions are functor images, enriched composition and simplicial
  restrictions. They request no fillers or fibrancy. Degenerate acting
  vertices and identity arrows are not excluded.
- The universe u is explicit and unrestricted; the actual cone mapping
  simplicial sets and old mapping simplicial sets have the same smallness
  universe as K. There is no accidental universe equality between unrelated
  categories, and no test-category quantification below its input universe.

Searches actually run with msearch.py for Q41 and this item:

- LeanFinder: `A triangle in a simplicial set induces a square of coning edges
  in coherent realization with minimal marked edges` returned eight hits,
  headed by `SSet.horn₂₂.sq`, `SSet.horn₂₁.sq`, `SSet.horn₃₂.desc` and
  `SSet.horn₂₀.sq`. These are subcomplex lattice squares and horn colimit maps,
  not squares in coherent cone mapping sets or their minimal marking.
- Loogle: `SimplicialThickening, Path` returned zero hits and the note
  `unknown identifier 'SimplicialThickening'`. This is an unsuccessful query,
  not evidence that Mathlib lacks subset paths: their actual source was read
  and they are used, rather than redefined.
- Mathlib grep via msearch: `coningEdge|coneTriangle|rigidification` returned
  zero hits. The lower-level subset-path nerve and CompStruct source were
  then opened directly and reused.
- LeanSearch: `A triangle in a simplicial set gives a square in the coherent
  cone mapping simplicial set` returned eight unrelated hits including
  `CochainComplex.mappingCone.triangleMap_hom₁`, `triangle_mor₂`,
  `CategoryTheory.CommSq.cocone`, and cochain mapping-cone triangle objects.
- Direct rg in the upstream WeilConjectures tree, current lean/Sheaf and
  dag/lean_names_upstream.json for the new namespace/declaration and triangle
  cone square names found no exact statement; upstream grep for the item id
  found none. Broader current-library searches did find the already recorded
  MarkedConeExternalProduct and MappingSimplexConeFibers constructions.
  Their full relevant signatures were read: they mark mapping objects in
  straightening pushouts, whereas this node concerns P=C[K star Delta[0]]
  itself. Neither states this triangle-square theorem. Their concrete
  PinchedCube realization is not copied; this module instead uses exactly
  the realization field of the item's recorded coherent-nerve dependency.

No STATEMENT-DISPUTED issue remains. No node fault or source correction was found.

Compilation evidence: scompile.py Q41 lem-coef-cone-triangle-mapping-square
was run on this module. The first run typechecked and reported two unused binder
warnings on structure fields. Those binders were renamed `_e` and `_σ` without
changing their types. The next per-file run succeeded with no warnings or errors:
sandbox pass 3.8 seconds; module pass 3.4 seconds; the default 60-second limit
was retained. No local direct Lean, Lake build or global build was run.

## Second reading by Q41

This is the author's completed second reading with the node, module and cited
source open; the maintainer's delivery review remains the independent reading.
No second agent was launched, as required by the dispatcher's brief.

I checked the entire node against the final source, beyond checking compilation.
The P/X_x clause uses the actual cone realization, with the inclusion image of x
as source and the new point as target. The action has the old arrow first and
cone arrow second, as required by precomposition. The baseEdge and coneArrow
normalizations use full subset vertices; the two interval normalizations use
`{0,2}⊆{0,1,2}` in the coned edge and input triangle respectively. This checks
both that rho points from k to fe and that tilde-e points from tilde-x to
e-star tilde-y. No unnormalized map or arbitrary marking is left in these data.

I then read IsSquare in coordinate order. Its four corner evaluations match
00,10,01,11, and its restrictions use fixed SECOND coordinate for bottom/top
and fixed FIRST coordinate for left/right. The top formula uses the degree-one
rho and the degenerate tilde-z, not constant rho or an input edge of K. The right
formula uses the fixed vertex e acting on the entire tilde-f. The four
precomposed-boundary equations use this same H, so there is no independently
chosen square with only matching corner data.

I checked the two marking conclusions against markedValue: its generator uses
a degenerate raw input edge and an arbitrary degree-one acting simplex, whereas
the preservation assertion correctly uses an arbitrary degree-zero acting
vertex. The two are not interchanged. The conditional clause has exactly the
node's premise that k is degenerate. Finally, I checked that CompStruct includes
every degenerate triangle, K has no Kan instance, and the empty case is not
excluded. The explicit table above covers every hypothesis and clause.

The only mismatch found during elaboration was the compiler's unused binder
naming, repaired as described above. No mathematical mismatch was found on the
second reading, and the informal statement remains unchanged. H1 is repaired
by the module and required report sections; H2 by the complete exact lean record
and lean-only node change; H11 by this source-specific clause-by-clause rereading
and the actual per-file scompile evidence.

Delivery validation: deliver2.py Q41 lem-coef-cone-triangle-mapping-square
--no-push printed `OK (dry run): commit 0e27042696 passes the preflight and
compiles; nothing pushed`. Its staged set contained exactly this module, the
item node and the report. All H1/H2/H11 return points have concrete repairs.

## Repair of packaging return at 7f8685f46377

The return reports an `--apply-fixes` path rejection for the installed report
`coord/reports/Q41/lem-coef-cone-triangle-mapping-square.md`; it identifies no
mathematical or Lean defect. The worker packet keeps the report at the required
sandbox `report.md`, the module at
`lean/Sheaf/AlgebraicTopology/ConeTriangleMappingSquare.lean`, and the node at its
DAG path. It is delivered through `deliver2.py`, not as an `--apply-fixes` input.
The prescribed initial dry run on the retained packet passed: commit bdf8106ab5,
with exactly the module, item node, and installed worker report staged.

I reread the current node and final module, including every corner and full
boundary of `IsSquare`, both marking conclusions, and the four precomposed
boundaries of the same square. I reread the current dependency realization
interface; its subset-simplex normalization and enriched composition remain
the interfaces used by this module. Empty K, repeated vertices, degenerate
triangles, and arbitrary non-Kan input remain included. A direct check confirms
that the node signature is verbatim, all thirteen declarations are recorded,
all lines meet the 100-character limit, and the sole postponed proof is the
named theorem. Comparison with the current base node confirms that only `lean`
changes. No mathematical changes are needed for the packaging diagnostic.


## Independent maintainer second reading, 2026-10-17

I independently reviewed immutable delivery
70cb7c8ea7c98b07b3d77139090fbd3a943308e6 against the item, all three
statement-dependency nodes, their actual Lean interfaces and the online IAS HTT
source. This is independent of the author's rereading above. The clause table in
the Worker report is accurate: I checked each entry against the delivered module.

In particular, `simplex` uses the dependency's equality-normalized realization,
`value` is the mapping simplicial set in the actual ordered right cone, and
`action` is enriched composition after the old-factor inclusion. The four
normalization fields of `CanonicalEdges` pin complete simplices, not only their
endpoints. Their finite subset-path test spaces are nonempty, so the universal
normalizations are not vacuous. No arbitrary-map hypothesis or choice from an
undetermined existence assertion is used.

I recomputed the subset square: its corners are {0,3}, {0,1,3}, {0,2,3},
{0,1,2,3}. The bottom/top restrictions vary the first coordinate, and the
left/right restrictions vary the second. These give precisely the four entire
edge equalities of `IsSquare`, with rho directed from the long edge to the
composite. `markedValue` has exactly the specified degenerate edges and diagonal
action generators. The top edge uses rho acting on the degenerate cone arrow;
it is the generator with d=s0(z). If k is degenerate its coning edge is degenerate.
Associativity gives marking preservation under every fixed old mapping vertex,
and `IsPrecomposedSquare` restricts the same composite H followed by precomposition.

The empty simplicial set, a point, arbitrary repeated vertices, s0/s1 triangles,
degenerate long edges and acting arrows, and non-Kan inputs are included. The
single universe u is arbitrary and agrees with the smallness convention of the
recorded realization; no independent universes are silently equated. There are
no extra instances or finiteness/nonemptiness assumptions.

Independent rg searches for coning, triangle squares and cone markings in the
project, upstream and Mathlib found no duplicate theorem. I inspected the related
`MarkedConeExternalProduct` and `MappingSimplexConeFibers` declarations: those use
the PinchedCube straightening pushout, not this dependency's realization package.
The shared underlying notions (marked simplicial sets, subset paths, ordered
join, edges and composition witnesses) are reused rather than redefined.

The record's statement equals the theorem signature verbatim. All thirteen
explicit declarations are recorded, all lines are at most 100 characters, every
declaration has source/blueprint documentation, and the theorem docstring covers
all five node proof steps. The sole postponed theorem has proof `sorry`; all
definition data are present. There is no statement correction, new independent
notion, missing prerequisite or dependency-interface repair needed.

Reproduction used only the prescribed command:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q41
lem-coef-cone-triangle-mapping-square <immutable snapshot module>`.
It exited 0, without errors or warnings: sandbox 2.4 seconds; library 2.9 seconds;
the printed per-file limit was 60 seconds. The installed wrapper currently
routes to the server's private side overlay, whose output identified
`/dev/shm/nt-tmp/nt-local-compile-l0vw1gzm/.lbuild`. I did not invoke direct SSH,
Lean, Lake, a global build, preflight or delivery/merge commands, and did not edit
a project clone or change the delivery head.

The only correction is restoring the three corrupted HTT citation numbers in
the report's Source read paragraph. The mathematical source is HTT 1.1.5.1 and
1.1.5.3 (subset paths and direct images), Notation 3.2.1.1 and Definition 3.2.1.2
(printed pp.170--171), and the first square in Proposition 3.2.1.11(4) (p.175).
That proposition uses Kan K to choose an inverse triangle; the present square
construction for an already supplied triangle needs no such assumption. No Lean
module or node record changes are required.
