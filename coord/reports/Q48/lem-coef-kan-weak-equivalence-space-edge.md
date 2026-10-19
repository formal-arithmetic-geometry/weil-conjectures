## Worker report

The module `Sheaf.CategoryTheory.KanWeakEquivalenceSpaceEdge` states
`CategoryTheory.Spaces.kan_weak_equivalence_space_edge`. It also supplies the explicit
canonical value-universe inclusion needed by the node's final clause. All data are real:
vertices and subset paths are relabeled, and every parametrized function is conjugated
by ULift.down and ULift.up. Only the main theorem and six named well-definedness
statements are postponed (three naturality statements extracted by the maintainer reader). Their docstrings give the respective complete proof plans.

Hypothesis and clause correspondence:

- W-small simplicial sets A and B: `{A B : SSet.{u}}`.
- Both Kan conditions, with no inhabitance or connectedness assumption:
  `[SSet.KanComplex A] [SSet.KanComplex B]`.
- The given simplicial map: `(f : A ⟶ B)`.
- Realization component bijection and all positive based homotopy-group isomorphisms:
  `hf : SSet.Enhanced.IsWeakHomotopyEquivalence f`. The recorded definition explicitly
  uses `componentsMap`, `homotopyGroupMap`, every degree r >= 1 and every source basepoint.
- The actual specified edge of f: existential `e` with
  `SSet.Enhanced.RightFibrationLimit.IsSpaceEdge f e`. This fixes both endpoint Kan
  complexes and the WHOLE enriched map on the interval Hom, as the constant vertex of
  the internal functor object. An arbitrary unrelated edge is insufficient.
- A simplicial inverse g: `g : B ⟶ A`, with edge d identified by `IsSpaceEdge g d`.
- The two actual triangles: `t s : infinityCategory _⦋2⦌`.
- First boundary (f,g,1_A): the equations for delta 2, delta 0 and delta 1 of t.
  The last is the degeneracy of delta 1 of e, hence the identity at A. These faces
  force the vertex triple (A,B,A).
- Second boundary (g,f,1_B): the three corresponding equations for s, with long edge
  the degeneracy of delta 0 of e, hence the identity at B and vertices (B,A,B).
- In particular e is an equivalence: `SSet.Enhanced.IsEquivalenceEdge infinityCategory e`.
- Any containing value universe: independent universe v and target value level
  `max u v`. `spaceUniverseLiftSimplex` is the literal inclusion on each enriched
  simplex. The final seven conjuncts assert exactly the six boundary equations for
  the images of THESE SAME t and s, and equivalence of the image of THIS SAME e.
  `spaceUniverseInclusion` assembles these maps into the canonical simplicial map
  from the degreewise ambient lift of the original coherent nerve. Nothing chooses
  an arbitrary comparison map or just some equivalent edge.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.IsEquivalenceEdge`,
  `IsWeakHomotopyEquivalence`, `diagramVertex`.
- `Sheaf.CategoryTheory.InfinityCategoryOfSpaces`: `CategoryTheory.Spaces.Kan`,
  `kanEnrichment`, `infinityCategory` (the actual Mathlib subset-poset coherent nerve).
- `Sheaf.CategoryTheory.RightFibrationSectionLimit`:
  `SSet.Enhanced.RightFibrationLimit.IsSpaceEdge`. Its already-landed node is added
  to stmt_deps; a graph traversal found no path from it back to this item.
- Proof-only import `Sheaf.AlgebraicTopology.KanWhiteheadInverse`:
  `SSet.Enhanced.kan_whitehead_inverse`, whose full signature and proof docstring were read.
- Coherent-nerve infrastructure has an explicit proof-only import, as well as being
  imported transitively by the recorded space module.
  The proof-only inverse-triangle node has no Lean record at preparation time and
  therefore contributes no import; its proof is cited in the main docstring.

Edge cases: the component condition forces both A and B empty if either is empty;
there is no choice of a point in the statement or universe construction. Disconnected
complexes retain all basepoints and all components. Identity maps have the expected
identity triangles. Universe v=0 includes the original value level, and arbitrary v
allows every larger value universe without forcing equality of site or value levels.
Degeneracies in the universe map preserve repeated vertices and singleton paths.

Searches (2026-10-17):

- msearch.py leanfinder, "A weak homotopy equivalence of Kan complexes is an equivalence
  edge in the coherent nerve": 8 hits, all ordinary nerves/homotopy-category interfaces;
  none is this assertion.
- msearch.py loogle, "CategoryTheory.SimplicialNerve, SSet.KanComplex,
  WeakHomotopyEquivalence": 0 hits (last identifier unknown).
- msearch.py grep, "coherentNerve|weakEquivalence.*Kan|Kan.*weakEquivalence" in
  AlgebraicTopology: 0 hits.
- msearch.py leansearch, "weak homotopy equivalence Kan complexes coherent nerve inverse
  triangles": 8 hits, including ordinary nerve adjunction and model-category localization
  criteria, none a coherent-space inverse-triangle statement.
- rg of upstream WeilConjectures and lean/Sheaf for the item id: no existing declaration.
  Searches for enriched edges found the published IsSpaceEdge, reused rather than copied.
  Searches for universe-lift constructions found successor-only density helpers in
  `SpaceYonedaDensity`. A DAG traversal gives a path from that node through transport
  classification, coherent-nerve comparison, model rectification, localization, pointwise
  adjunction and pointwise Yoneda back to THIS item. Importing it would close a cycle.
  The generalized construction here permits arbitrary v, uses distinct names, and is
  part of the present node's explicit universe clause; no downstream theorem is assumed.

Sources checked online: https://kerodon.net/tag/06QR (mapping spaces of the coherent
nerve of Kan complexes) and https://kerodon.net/tag/00M5 (inverse triangles and enriched
homotopies). Mathlib's SimplicialNerve source was read to verify its subset-inclusion
orientation; the proof uses the existing inverse-triangle node with that convention.
No natural statement correction and no disputed mathematical claim.

The previous BLOCKED diagnosis concerned Q114's completed stage-1 split. The node has
no lean/reviewed_lean record, so that split does not supersede this stage-2 assignment.

## Second reading by Q48

Independent maintainer reading of immutable delivery
cd3d04cb0df069fd51cf076ed951570ae4655ac9, performed after the assigned worker's
self-check. Read packet.md, check-brief2.md in full, the snapshot item and all three
statement-dependency records, the delivered module, and the exact dependency
source declarations and their docstrings in the read-only Q48 clone.

Clause audit:

- A and B are arbitrary SSet.{u}; both and only the two Kan instances are required.
- f is the given simplicial map. IsWeakHomotopyEquivalence unfolds to a path-component
  bijection and bijections on the induced positive based homotopy-group maps, for every
  source realization basepoint; these maps preserve the group operations.
- infinityCategory is SimplicialNerve Kan, using Mathlib's subset-poset coherent nerve.
  IsSpaceEdge f e fixes A, B and the whole enriched map at 01 by HEq with the constant
  diagramVertex f; it does not merely require an edge with those endpoints.
- The existential g has type B -> A, and d is its actual edge by the same predicate.
- t has faces delta2=e, delta0=d, delta1=sigma0(delta1(e)), so its vertices and
  boundaries are (A,B,A) and (f,g,id_A). The three analogous faces of s give
  (B,A,B) and (g,f,id_B). IsEquivalenceEdge is exactly this inverse-triangle condition.
- The six lifted face equations use images of the very same t, s, e and d, together
  with equivalence of the image of e. The explicit inclusion lowers finite vertex
  labels, pulls back their subset paths, and conjugates parametrized functions by
  ULift.down/up. Thus it identifies the actual lifted maps, rather than arbitrary ones.
  Independent v and max u v cover any containing value universe, with no equality or
  successor-only restriction.

Read Kerodon 06QR, 00UB, 03X7, 00M5, 00M0 and 01PF, and HTT 1.1.5 and
1.2.16. Checked the orientation against Mathlib SimplicialNerve: the inclusion
{0,2} subset {0,1,2} goes from the identity to the composite. The cited inverse-triangle
node supplies the needed reversal in the Kan internal Hom. The existing Whitehead
inverse declaration has exactly these hypotheses and supplies both cylinder homotopies.
The inverse-triangle node has no Lean record in this snapshot context, so there is
no module to import for it; a proof-only DAG prerequisite need not be restated merely
to state this theorem. The imported declarations needed for the signature all exist.

Edge cases: both complexes empty; exactly one empty (excluded by the component
bijection); disconnected and discrete Kan complexes; identity f; n=0 and repeated
vertices in the lift; v=0 and arbitrary larger v. No basepoint is selected.

Independent searches: Loogle query "SimplicialNerve" returns only the generic
CategoryTheory.SimplicialNerve. LeanSearch query "A realization weak equivalence
between Kan simplicial sets yields an invertible morphism in the homotopy coherent
nerve" returns generic weak-equivalence predicates, ordinary nerve homEquiv, truncated
homotopy-category functorEquiv and nerveAdjunction.isIso_counit, none a match. rg over
Mathlib AlgebraicTopology, WeilConjectures and the Q48 Sheaf tree finds the reused
coherent nerve, space and edge interfaces; the density universe-lift helpers are only
successor-universe constructions. DAG traversal verifies that importing their owner
would cycle back to this item. The added IsSpaceEdge owner has no dependency path
back to this item (412 reachable nodes checked).

Finding and repair: H6, with the named-proof rule in brief-stage2 section 2. The three
inline naturality proofs in spaceUniverseLiftHomSimplex, spaceUniverseLiftAction and
spaceUniverseInclusion were replaced by references to three named helper theorems
with sorry proofs, source/blueprint docstrings and explicit proof plans. These are
well-definedness statements for this node's universe-inclusion clause, not new
independent mathematical notions. All data formulas and the main signature remain
unchanged. The lean.declarations list includes the three new helpers. Added the module
main-declarations list required by section 3. No statement correction or dependency
repair was needed, and no assumptions or conclusion clauses were changed.

Validation: the installed prescribed scompile.py wrapper currently dispatches to the
server overlay. Original snapshot: sandbox compile 2.2 s and library compile 2.4 s,
exit 0, no diagnostics. Corrected module: sandbox compile 3.0 s and library compile
3.0 s, exit 0, no diagnostics (60 s per-file limits). A final recheck after the
module-docstring-only addition also passed: sandbox 4.2 s, library 3.6 s,
exit 0 with no diagnostics; pure check_lean_text returned no findings. The main
lean.statement is byte-for-byte the signature in both versions. All 14 declarations
have source/blueprint docstrings; every theorem body is sorry, no definition data
contains sorry, and every line is at most 100 characters. No global build, direct SSH,
Git mutation, project-clone edit or live Lean write was performed by the reviewer;
only the authorized compiler wrapper and review/fixes outputs were used.
