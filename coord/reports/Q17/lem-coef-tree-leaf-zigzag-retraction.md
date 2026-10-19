## Worker report

Repair of return L on head 01ef156de992. The former packet was a stage-1 report,
not a stage-2 statement. This packet adds the actual module
`Sheaf.CategoryTheory.Localization.TreeLeafZigzagRetraction`, the item's complete
`lean` record, and this clause-by-clause reading. It preserves the current node's
statement, proof, proof_deps and split_report verbatim. The only changes to that
node are lean and the addition of one landed statement dependency. No dependency
node is modified, and no independent missing notion needs a new node.

The sole postponed theorem is
`CategoryTheory.RelativeZigzag.tree_leaf_zigzag_retraction`. Every theorem proof is
`sorry`; the helper definitions have complete real data and contain no `sorry`.
The canonical functors are quantified with determining equations, not selected
from an uncharacterized existence theorem. The theorem can be used by unpacking
its witnesses; no definition chooses a witness from this postponed proof.

The statement is rendered as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small vertex set, without a finiteness hypothesis | `V : Type u`, with explicitly bound universe `u` |
| A direction for each edge, arbitrary orientation | `G : Digraph V`; `h_orientation : ∀ s t, G.Adj s t → ¬ G.Adj t s` forbids loops and both orientations. The underlying graph is `G.toSimpleGraphInclusive`, so each undirected edge is exactly one of the two possible directions. No directed-root hypothesis is imposed. |
| Nonempty underlying undirected tree with unique finite simple paths | `h_tree : G.toSimpleGraphInclusive.IsTree`. Mathlib's `SimpleGraph.isTree_iff_existsUnique_path` states precisely equivalence with nonemptiness and a unique simple walk between any two vertices; no finiteness of the entire tree is assumed. |
| Free path category, empty paths as identities | `Paths (TreeLeafVertex G)`, using Mathlib's `Paths.categoryPaths`: Hom is `Quiver.Path`, identity is `.nil`, composition is `.comp`. The quiver has exactly `PLift (G.Adj s t)` as its edges. |
| Leaf l, unique neighbour a | `h_leaf : ∀ v, G.toSimpleGraphInclusive.Adj l v ↔ v = a`. This includes adjacency to a and excludes every other neighbour. In particular it forces a ≠ l. |
| Delete l and its incident edge | `treeLeafDelete G l`, with vertices `{v : V // v ≠ l}` and adjacency inherited from G on their values. |
| Canonical inclusion i | Existential `i` with `IsTreeLeafCollapse`: its object is `v.val`; its value on every surviving generator is that same singleton path. By free-path uniqueness this is exactly the inclusion, with no freedom on longer paths. |
| Canonical collapse r | Existential `r` with `IsTreeLeafCollapse`: `(r.obj v).val = if v = l then a else v`; every surviving generator stays itself; every generator incident to l becomes `𝟙 (r.obj s)`, hence the empty path at a. These equations uniquely determine r on all paths. |
| Endpoints x,y different from l | `x y : TreeLeafVertex (treeLeafDelete G l)`; in the original category they are `x.val,y.val`. This ranges over exactly all pairs satisfying the node's two inequalities. |
| Every finite word in +,-, including empty | `w : List Bool` and existing `FixedHammockGraph.word w`: true means forward, false means backward. No length or alternation restriction. |
| Pair (C_T,C_T), identity arrows allowed | `RelativeZigzag.Diagram (⊤ : MorphismProperty (Paths ...)) ...`; backward and vertical arrows are all paths, forward arrows unrestricted, and the recorded Diagram permits identity arrows in every position. |
| Induced I_w and R_w | Existential `I,R` in the exact two diagram-category directions. `IsTreeLeafInduced` specifies every vertex and horizontal arrow by the existing `FixedHammockGraph.DiagramImage`, and every vertical component by `HEq ((H.map f).app j) (F.map (f.app j))`. Hence these functors are exactly the entrywise images under i,r. |
| Strict R_w I_w = 1 | `I ⋙ R = 𝟭 _`, literal functor equality in Lean's left-to-right composition convention. Also `i ⋙ r = 𝟭 _`. Neither equation is replaced by a natural isomorphism. |
| Edge l→a gives 1 ⇒ I_w R_w | For every `e : G.Adj l a`, there is `η : 𝟭 _ ⟶ R ⋙ I`. The component is the singleton path `e` whenever `objectAt ⊤ d j = l`, and the identity otherwise. |
| Edge a→l gives I_w R_w ⇒ 1 | For every `e : G.Adj a l`, there is `η : R ⋙ I ⟶ 𝟭 _`, with the same explicit leaf/other-vertex component rule. |
| Endpoint components identities | The component rule applies to every vertex, including `first` and `last`. The endpoints are x.val,y.val ≠ l, and `RelativeZigzag.Hom.left/right` additionally impose the recorded endpoint identity equations. Thus endpoint identities are part of the actual morphism type, not an informal promise. |

`HEq` compares morphisms whose sources and targets are identified by the preceding
object equations; it does not quotient morphisms or weaken a component formula.
Functor data is determined on generators by the free-path universal property;
diagrams are determined by their vertices and horizontal arrows (with proof
irrelevance for the empty endpoint equality), and their morphisms by all vertical
components. Consequently the existential formulation determines the canonical maps
completely, as the existing fixed-hammock-graph interface also does.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.Localization.ZigzagHomotopyCalculus`:
  `CategoryTheory.RelativeZigzag.Letter`, `Horizontal`, `Diagram`, `Vertex`,
  `objectAt`, `first`, `last`, `endpoints`, `Hom`, `diagramCategory`.
  In particular `Hom` requires commuting squares, membership of all components
  in W and both endpoint identity equations; its full source was inspected.
- Added already-landed node `lem-coef-fixed-hammock-graph-homotopy-invariance`:
  `Sheaf.CategoryTheory.Localization.FixedHammockGraphHomotopyInvariance`,
  `CategoryTheory.FixedHammockGraph.word`, `HorizontalImage`, `DiagramImage`.
  The full declaration and the node statement were read. Only its real helper
  definitions are used; its homotopy-invariance theorem is not invoked. This
  avoids a duplicate of the project's existing signed-word or diagram-image notions.
- Mathlib `CategoryTheory.PathCategory.Basic`: `Paths`, `Paths.of`,
  `Paths.categoryPaths`, `Paths.lift`, `Paths.lift_unique`, `Quiver.Hom.toPath`.
- Mathlib `Combinatorics.Digraph.Orientation`: `Digraph.toSimpleGraphInclusive`;
  `Combinatorics.SimpleGraph.Acyclic`: `SimpleGraph.IsTree`,
  `SimpleGraph.isTree_iff_existsUnique_path`.

Edge cases checked before writing:

- A singleton tree has no degree-one leaf, so cannot satisfy h_leaf; the theorem
  does not incorrectly claim a collapse to an empty category.
- For the one-edge tree in either orientation, deletion leaves the singleton a;
  the edge maps to its identity, and the natural-transformation direction agrees.
- The tree may be infinite; all paths and zigzag words remain finite, and no
  finiteness or local-finiteness instance is imposed.
- Empty word and unequal endpoints: both diagram categories are empty. With equal
  endpoints they have one diagram up to proof irrelevance and only its identity.
- Adjacent same-sign letters, identity horizontal paths, repeated occurrences of
  l, and words +- or -+ are all included; the component rule treats each vertex.
- Arbitrary mixed orientation on a three-vertex path is permitted; the undirected
  tree condition has not been replaced by directed arborescence.

Source grounding: opened the cited Dwyer--Kan PDF online, Section 5.8(iii), printed
p.25 (PDF p.9), and read the existing node's explicit auxiliary proof. That source
reduces the free W=C case to finite generators and induction; the leafwise expansion
is correctly identified as agent supplied rather than asserted to be verbatim DK.
Read the current main-20261015 blueprint unit and its biduality proof to check the
recorded ancestry. The module docstring and theorem docstring cite this source and
blueprint id and give every graph, diagram and naturality proof step.

Searches made:

- `msearch.py leansearch`, query: "Leaf collapse on fixed word zigzag categories
  in the free category on an oriented tree". Eight connectedness-zigzag results,
  including `CategoryTheory.Zigzag` and its constructors; none defines fixed-word
  diagram categories or leaf collapse.

- `msearch.py leanfinder`, query: "A leaf collapse of an arbitrarily oriented tree
  induces a strict retraction on fixed word relative zigzag categories". Eight
  results include `IsFreeGroupoid.SpanningTree.treeHom`, `loopOfHom`, `treeHom_eq`
  and `CategoryTheory.Zigzag.of_inv`; these concern free groupoids or mere
  connectedness, not a fixed-word diagram-category leaf retraction.
- `msearch.py loogle`, query: `CategoryTheory.Paths, CategoryTheory.Functor`.
  Twelve hits include `Paths.lift`, `Paths.lift_unique`, `Paths.ext_functor`,
  `Paths.liftNatTrans`, and `Cat.freeMap`. Reused free paths; no leaf-collapse
  zigzag result is present.
- `msearch.py grep`, query:
  `zigzag.*(tree|leaf)|(tree|leaf).*zigzag|leafCollapse`: zero Mathlib hits.
- `rg` of the project and upstream source for oriented tree, OrientedTree,
  leafCollapse, and tree/leaf combined with zigzag: no matching theorem; the
  parent free-factor hammock proof mentions the argument without defining it.
  `grep -rn` for the node id in upstream returned no hits. The upstream name
  inventory also has no collision with the new declaration names.
- `rg` of the existing RelativeZigzag modules found and reused the landed
  FixedHammockGraph helper definitions instead of introducing copies.

No statement correction or statement dispute is needed. No statement of a target,
unit, dependency, or citer is changed.

## Second reading by Q17

This is a separate second pass over the final node and module by the same worker;
no independent worker was started, as required by the dispatcher. Independent
review remains the maintainer's. This pass is an actual reading, not the stage-1
"Review by Q17" that appeared in the returned packet.

I reread the node hypothesis by hypothesis and matched it to the table above.
The orientation condition forbids both loops and opposite directed copies of the
same edge while leaving all tree orientations possible. `IsTree` is the undirected
nonempty unique-path condition, not an arborescence. The leaf-neighbour iff and
subtype endpoints give precisely one incident edge and x,y ≠ l. Paths are the
Mathlib free path category, and W is top in both source and target diagrams.
The functor specification fixes i on all retained generators, r on retained and
incident generators, and r on all objects, so the witnesses cannot be unrelated
retractions. The induced-functor specification includes horizontal and vertical
arrows, not just objectwise vertex images. I ⋙ R is the strict identity, while
R ⋙ I has exactly the requested transformation direction in each orientation.
Every transformation component is the edge at the leaf and the identity elsewhere;
first/last are included and Hom enforces endpoint identities. No word-length
restriction excludes the empty word. The only sorry is the theorem matching this
DAG node, with the complete five-step proof plan in its docstring.

This pass caught two syntactic interface issues before final compilation: the
classical equality decision belongs outside the collapse-specification docstring,
and Quiver.Hom.toPath's endpoint binders are a,b (not X,Y). Both were corrected. The first server compile reported exactly those two
issues (Decidable equality and toPath endpoint names); neither required any
mathematical statement change. Explicit generator endpoints were also supplied
to keep elaboration direct.
The report, module and verbatim Lean record now carry substantive stage-2 content;
no split_report change from the rejected stage-1 packet is retained.

Validation: `scompile.py Q17 lem-coef-tree-leaf-zigzag-retraction` completed with
exit 0 for this file, both as `Sheaf/Stage2/Sandbox0.lean` and as the delivered
module. Both compiler outputs contain no errors or warnings. The wrapper retains
the 60-second Lean-process limit; its printed elapsed times include slot waiting.
The final node record's statement is the exact multiline theorem signature from
the file, and its declarations list includes every helper and the main theorem.

## Maintainer fix (stage-2 review of c0513807b7c4)

The delivered mathematics is correct (see review.md). One finding, H4: the
landed node `def-coef-oriented-tree-subtree-zigzags`
(`Sheaf.CategoryTheory.Localization.OrientedTreeZigzags`, landed in the stage-2 batch
2f2b5c687a, four minutes after this delivery's commit) already gives the notion this
node introduces in its first two sentences, in the same words: `OrientedTree`
(nonempty undirected tree, exactly one direction per edge), `Vertex`, `vertexQuiver`,
`PathCategory` (Mathlib `Paths`) and `signedWord`. The sibling
`lem-coef-tree-zigzag-finite-subtree-colimit`, which the parent free-factor proof
combines with this lemma, is stated on it. The delivery's Digraph rendering
(`TreeLeafVertex`, `treeLeafQuiver`, `treeLeafDelete`, `h_orientation`, `h_tree`) was a
second definition of the same notion.

Changes, nothing else:

- The theorem takes `T : OrientedTree V` and `h_leaf : ∀ v, T.graph.Adj l v ↔ v = a`;
  `OrientedTree` contains the tree, orientation and asymmetry hypotheses.
- `TreeLeafVertex`/`treeLeafQuiver` are removed in favour of `OrientedTree.Vertex`,
  `vertexQuiver` and `PathCategory`. Generators are `ULift.up (PLift.up e)`.
- `treeLeafDelete` is replaced by the real construction `OrientedTree.deleteLeaf`:
  vertices `{l}ᶜ`, the induced graph, the restricted directions. Its tree proof is
  complete (Mathlib `Connected.induce_compl_singleton_of_degree_eq_one`, with a
  `Fintype` neighbour set `{a}` from `h_leaf`, and `IsAcyclic.induce`). It is not
  hollow and has no `sorry`.
- The words are `OrientedTree.signedWord w` (identical in content to
  `FixedHammockGraph.word`). `IsTreeLeafInduced` still uses the landed
  `FixedHammockGraph.DiagramImage`.
- `IsTreeLeafCollapse`, `IsTreeLeafInduced`, the conclusion clauses, their order, the
  transformation directions and the component rule are unchanged.

Compile: `nt_compile.py` (json mode, side overlay) gives rc 0 with no messages for the
fixed module. A scratch copy shows that the compiler reports errors, and that
`Paths.lift` of the vertex inclusion meets the `i` clauses of `IsTreeLeafCollapse`.
The item's `stmt_deps` should also gain `def-coef-oriented-tree-subtree-zigzags`,
which is landed with a lean record, does not reach the item, and so makes no cycle.
The lean.note records this.
