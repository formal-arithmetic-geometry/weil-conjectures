## Worker report

The module `Sheaf.AlgebraicTopology.MappingSimplexConeFibers` states
`SSet.Enhanced.mapping_simplex_cone_fibers`. It defines the canonical marked cone
values, their precomposition action and diagram, the point version T, and the
specified fibre map. All theorem proofs are `sorry`; every definition has actual
data. The auxiliary theorem statements are construction well-definedness laws of
this node, carry its blueprint tag, and have individual natural-language proofs.
The main theorem's docstring follows all ten proof steps of the node.

Source read: Lurie, Higher Topos Theory, Definition the project server, Remark the project server,
the displayed psi before Lemma the project server, and Lemma the project server with its induction.
The node's HTT.pdf address timed out; the same book was successfully opened at
https://www.math.ias.edu/~lurie/papers/highertopoi.pdf, printed pp. 171 and 189–191
(PDF pp. 188 and 206–208). This verifies both the action-marking convention and
the particular comparison map, rather than an arbitrary weak equivalence.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small simplicial set S | `{S : SSet.{u}}`, for arbitrary explicitly bound `u` |
| Marked X mapping to S | `(X : Marked.{u}) (a : X.underlying ⟶ S)`; mapping to sharply marked S imposes no additional restriction |
| Coherent realization | Reuses the landed colimit extension `PinchedCube.rigidification`, built from Mathlib's subset-poset `SimplicialThickening` |
| P_X = C[S] amalgam C[X star point] over C[X] | Existing `Straightening.conePushout a`, using precisely those two realization maps |
| New cone vertex v | Existing `Straightening.coneVertex a`, the image of the pure last join vertex |
| L_S(X)(c) = P_X(c,v) | `markedValueAt X a c` has underlying `Straightening.valueAt a c` |
| Precomposition action and opposite indexing | `markedPrecomposition X a c d` has domain `sharp(C[S](d,c)) × L(c)` and target `L(d)`; `markedConeDiagram X a` packages the corresponding ordinary diagram on `ForgetEnrichment SSet C[S]ᵒᵖ`. Its full simplicial action is the preceding marked precomposition map, with underlying laws inherited from `straightening a` |
| Coning triangle of e:x→y | `coneEdgeTriangle a e` realizes the actual joined edge simplex into the cone pushout; `coneTriangleInterval` is the nerve edge `{0,2} ⊆ {0,1,2}` in C[Delta2](0,2) |
| Edge tilde-e from direct cone arrow to e*tilde-y | `coningEdge a e` applies that triangle's map on hom(0,2), with only the endpoint identifications from `coneEdgeTriangle_endpoints` |
| Mark g*tilde-e for marked e and every base mapping-space edge g | The second disjunct in `markedValueAt.marking` quantifies `e ∈ X.marking` and `g : hom C[S] c (vertex (a(delta1 e))) _[1]`, then applies the actual `precomposition` map |
| Include all degenerate edges | The first disjunct is `Set.range ((valueAt a c).σ 0)`; the structure's `degenerate` field explicitly inserts that disjunct |
| Same construction over a point, with terminal index | `markedPoint X` is `markedValue X` over `Delta0`, at its unique vertex. The coherent realization of Delta0 is the terminal simplicial index; its presentation is the same existing rigidification convention as for every base |
| Every n≥0 | `(n : ℕ)`, including 0 |
| Every reversed chain A0←...←An | `(A : SimplexChain.{u} n)` is the recorded functor `(Fin (n+1))ᵒᵖ ⥤ SSet.{u}` |
| Every 0≤i≤n | `(i : Fin (n+1))` |
| Marked mapping simplex M^m(A) and its projection | Reuses `markedMappingSimplex A` and `mappingSimplexProjection A`; no replacement or fibrancy hypothesis |
| Source T(A_i^flat) | `markedPoint (Marked.flat (A.obj (op i)))` |
| Inclusion of the vertex fibre | `mappingSimplexMarkedFiberInclusion A i` has underlying exactly the recorded `mappingSimplexFiberInclusion A i` |
| Specified cone-pushout universal map, identity at i | `mappingSimplexConeFiberMap A i` uses `markedValueMap` for that inclusion and the point-to-Delta-n vertex map; its underlying map is the existing `valueMap`, constructed from `conePushoutMap = pushout.map`. The only final transport identifies the image of the unique point vertex with i; there is no extra base arrow or chosen inverse |
| Weak equivalence in the absolute marked model | `Marked.weak (mappingSimplexConeFiberMap A i)` is exactly the recorded absolute mapping-test definition, not a relative or underlying weak-homotopy equivalence |
| Natural for maps of chains | The second conjunct quantifies every natural transformation `h : A ⟶ B` and asserts the strict square `mappingSimplexPointMap h i ≫ psi_B = psi_A ≫ mappingSimplexConeChainMap h i`. The mapping-simplex map sends `(alpha,z)` to `(alpha,h_alpha(last)(z))`; the point map uses `h_i`, and the cone map uses the identity of Delta-n |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CartesianMappingSimplexPresentation`:
  `SSet.Enhanced.SimplexChain`, `MappingSimplexDegree`, `mappingSimplexOperator`,
  `mappingSimplex`, `mappingSimplexProjection`, `mappingSimplexFiberInclusion`,
  `markedMappingSimplex`, and their recorded naturality/projection interfaces.
- `Sheaf.CategoryTheory.CoherentNerveComparison`:
  `CategoryTheory.CoherentNerveComparisonStatement` and its realization convention;
  its infrastructure provides `CoherentNerve.SCat` and `CoherentNerve.hom`.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, `Marked.flat`, `Marked.sharp`, `Marked.product`,
  `Marked.flatMap`, `Marked.weak`, and the model statement's absolute conventions.
- Added the already landed owner `lem-coef-right-straightening-fiber-comparison`
  to statement dependencies and imported
  `Sheaf.AlgebraicTopology.RightStraighteningFiberComparison` publicly. Used
  `SSet.Straightening.simplexInclusion`, `vertex`, `conePushout`, `coneInclusion`,
  `baseInclusion`, `coneVertex`, `valueAt`, `value`, `precomposition`,
  `straightening`, `conePushoutMap_vertices`, and `valueMap`. These are actual
  pushout constructions and their defining laws; the unmarked weak-equivalence
  theorem is not an assumption or an argument proving the marked result.
  Its transitive imports provide `PinchedCube.coherentSimplex`,
  `PinchedCube.rigidification`, and `Enhanced.joinPointTopSimplex`.
- Available proof-only owners are imported without `public`:
  `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus` and
  `Sheaf.AlgebraicTopology.MarkedTriangleCancellation`. The other recorded
  proof-only nodes (projective-model calculus, monomorphism boundary cells,
  marked-cone generator calculations and marked-cone external product) have no
  recorded Lean module in the inspected DAG and therefore cannot yet be imported.
  They do not occur in this statement's types. The maintainer can add their
  proof-only imports when they are stated. The main docstring names their exact
  roles without assuming a straightening equivalence.

No new definition node or dependency repair is needed: the missing marked
construction is explicitly introduced by this item's own statement. Its helpers
belong to that construction. The additional dependency owns the existing
unmarked construction and prevents a second private definition. A traversal of
all statement/proof dependencies of this added owner found no path back to this
item (181-node closure).

Edge cases checked before writing:

- n=0 has one vertex and no chain transition; the comparison is the point-cone
  identification. There is no positivity assumption on n.
- Empty A_i and even entirely empty chains are admitted: no vertex, section,
  nonemptiness, Kan or quasicategory hypothesis is added. Cone mapping sets from
  the old point are empty when the fibre is empty.
- The last vertex i=n is admitted and the induction proof identifies its map
  with the canonical isomorphism. The statement asks only the source's weak
  equivalence; it does not add that stronger conclusion as a conjunct.
- All chain maps, including maps with empty source fibres and noninjective
  transitions, are allowed. The map is not defined using a fibre inverse.
- The marking includes arbitrary 1-simplices g, not just degenerate base arrows;
  flat fibre marking and sharp base-action marking are kept distinct.
- Universes are explicitly bound; the arbitrary universe u governs both the
  small input simplicial sets and their coherent categories. No universe
  equality, fibrancy, local Kan or nonemptiness hypothesis is imposed.

Searches made (all via the prescribed wrapper or read-only rg):

- LeanFinder: `vertex fiber marked mapping simplex cone straightening weak equivalence`.
  Eight hits, on standard-simplex faces, horns and pointed simplices; none state
  the marked cone-fibre theorem or construct the marked diagram.
- Loogle: `SSet, pushout`. No hits; service reported unknown identifier `pushout`.
- Mathlib grep: `mappingSimplex|markedCone|coneDiagram|straightening`.
  Zero hits.
- LeanSearch: `marked simplicial cone straightening functor`. Eight hits including
  generic simplicial sets, nerve and simplicial hom functors, with no match.
- Project rg in WeilConjectures for mapping-simplex, marked-cone and straightening
  names, and direct search for this blueprint id: no matching construction or
  theorem. The upstream declaration-name index has no proposed-name overlap.
- Project rg in lean/Sheaf for marked-cone and straightening names located
  `RightStraighteningFiberComparison`; read its entire construction and reused it.
  Searches for the proposed `markedValueAt`, `markedConeDiagram`,
  `coneTriangleInterval`, and `mapping_simplex_cone_fibers` found no duplicate.
- DAG inspection found related generator and external-product theorem nodes
  describing the same construction but with no Lean declaration, and the
  unmarked comparison node above. No distinct existing marked-cone definition
  node needs to be recreated.

There is no statement correction and no STATEMENT-DISPUTED issue. The naturality
clause and canonical-map requirement are retained explicitly.

## Second reading by Q61

I independently opened the node, the complete proposed module, the four statement
prerequisites and their declaration sources. I read HTT Definition the project server,
Remark the project server, the construction of psi immediately before Lemma the project server, and
that lemma's induction on printed pages 189–191 in
https://www.math.ias.edu/~lurie/papers/highertopoi.pdf. This is an HTT source,
not a Stacks result. No extra ambient fibrancy or nonemptiness assumption is
present in the source lemma. The proposed statement agrees with the node and
source; I found no mathematical mismatch and changed no Lean or node text.

My inventory and item-by-item comparison follows. Each entry passed.

1. Arbitrary small simplicial base S and marked X with X -> S:
   `{S : SSet.{u}} (X : Marked.{u}) (a : X.underlying ⟶ S)` in
   `markedValueAt`. A map to the sharp marking on S has precisely this data;
   the signature does not add a marking condition on the base.
2. Coherent realization, pushout P_X and its new vertex v:
   `PinchedCube.rigidification`, `Straightening.conePushout a` and
   `Straightening.coneVertex a`. I read the actual definitions: rigidification
   is the colimit extension of the subset-poset coherent simplices; the pushout
   has the realized join-inclusion and a as its two legs; its distinguished
   vertex is the pure final join vertex. These are reused constructions.
3. Values P_X(s,v) and contravariant simplicial action:
   `markedValueAt.underlying := valueAt a c` and
   `markedPrecomposition X a c d`, whose source is the product of sharply
   marked hom(d,c) and the value at c, and whose target is the value at d.
   The ordinary diagram `markedConeDiagram` packages these values and their
   vertex actions on the opposite realized base. Its full simplicial action
   is supplied separately by `markedPrecomposition`, with the actual
   precomposition maps and the inherited enriched unit/composition laws.
4. Coning triangle for each edge e:x->y and its directed edge:
   `coneEdgeTriangle` uses `joinPointTopSimplex 1` and the join map of e with
   the point identity. `coneTriangleInterval` is the inclusion of the direct
   endpoint path {0,2} into {0,1,2}; thus `coningEdge` has the required
   direct-to-composite orientation. Its only transports identify the source
   vertex with a(x) in the pushout and the target with the new cone vertex.
5. Exactly the prescribed marking: the second disjunct of
   `markedValueAt.marking` is an image of `(g, coningEdge a e)` under the
   actual precomposition map, with e marked in X and g an arbitrary
   1-simplex of hom(c,a(x)). The first disjunct adds exactly degeneracies.
   In particular g is not restricted to vertices or degenerate edges.
6. Point construction T with terminal index: `markedPoint X` uses the unique
   map to Delta[0] and its unique vertex, with the same `markedValue` formula.
   This is the terminal-base specialization, without selecting an unrelated
   point functor or an arbitrary comparison equivalence.
7. Every integer n>=0, reversed chain A and vertex i:
   `mapping_simplex_cone_fibers (n : ℕ)`, `A : SimplexChain.{u} n`, and
   `i : Fin (n+1)`. The dependency's `SimplexChain` is exactly
   `(Fin (n+1))ᵒᵖ ⥤ SSet.{u}`. Its mapping simplex uses the final-fibre
   coordinate, its projection keeps the base coordinate, and its marking is
   degeneracy of that fibre coordinate. I checked these definitions directly.
8. Flat vertex fibre, canonical inclusion and required particular map:
   `mappingSimplexMarkedFiberInclusion` has underlying precisely the recorded
   `mappingSimplexFiberInclusion`. `mappingSimplexConeFiberMap` has source
   `markedPoint (Marked.flat (A.obj (op i)))` and target the marked mapping
   simplex's cone value at i. It applies `markedValueMap` to that inclusion
   and the vertex map Delta[0] -> Delta[n]. I followed `valueMap` to
   `conePushoutMap = pushout.map`; the final transport only identifies the
   image of the point vertex with i. No nonidentity index prefix is inserted.
9. Absolute marked weak equivalence for every chain and vertex: the first
   conjunct is `Marked.weak (mappingSimplexConeFiberMap A i)`. I read
   `Marked.weak`: it tests sharp mapping objects against every small
   quasicategory with its natural marking. This is the absolute marked model,
   and neither a relative equivalence nor an underlying Kan equivalence.
10. Naturality for every map of chains: the second conjunct quantifies arbitrary
    `A B`, `h : A ⟶ B` and i and equates the two composites in the required
    square. `mappingSimplexChainMap` applies the final component of h to the
    fibre coordinate; `mappingSimplexPointMap` applies h_i; and
    `mappingSimplexConeChainMap` fixes Delta[n]. This matches strict naturality
    of the specified maps, with the same quantifier scope as the node.

Edge cases: n=0 and i=n are admitted, as are empty fibres and the entirely empty
chain. A chain has n+1 indices, so an empty index type is not part of this node;
empty simplicial values are allowed. The construction of L also admits empty S
and empty X, with no base object required unless a value is requested. No ring,
characteristic, scheme, Kan, quasicategory, positivity, injectivity, or section
hypothesis was introduced. Universe u is arbitrary and explicitly bound; the
same input-size convention as the recorded coherent realization is used, with
no extra universe equation or instance parameter. `autoImplicit false` and the
successful compile confirm that no variable is left unbound.

Independent H4 searches: I ran LeanFinder for `marked straightening mapping
simplex vertex comparison Cartesian equivalence` (eight unrelated pointed
simplex/standard-simplex hits), and LeanSearch for `Marked simplicial set
straightening cone fiber over a vertex` (eight unrelated simplicial or ordinary
fibre hits). I searched Mathlib and WeilConjectures with rg for `straighten`,
`marked.*cone`, `mappingSimplex`, `MappingSimplex`, and `coningEdge`; no match.
I also searched lean/Sheaf for the proposed definitions and theorem, and the
upstream declaration-name index for their names: no duplicate. The existing
unmarked straightening module is correctly reused, rather than redefined.
The additional landed statement dependency owns those constructions; an
independent traversal of its statement/proof closure finds no cycle to this
item. There are no new definition nodes or dependency-module repairs to audit.

H5–H9: definitions have explicit data; the postponed endpoints, preservation and
functoriality laws are named theorem statements belonging to this construction,
with source/blueprint citations and proof explanations. Every theorem proof is
`sorry`. The main docstring follows all ten node proof steps, including the
endpoint two-out-of-three argument and induction, without invoking the
straightening equivalence. Available proof-dependency modules are imported;
the four unavailable proof-only modules listed in the worker report remain
unimported. All lines satisfy the 100-character limit. I mechanically verified
that `lean.statement` is verbatim the main signature and that only the permitted
node fields differ from the repository record.

Validation: the prescribed scompile.py wrapper compiled this delivered module
as both sandbox and library module cleanly (2.7 s and 2.5 s respectively), with
no diagnostics. My first compile invocation used a relative file path outside
the sandbox and failed before Lean; repeating with the absolute sandbox file
path succeeded. No source repair or statement correction was necessary.
