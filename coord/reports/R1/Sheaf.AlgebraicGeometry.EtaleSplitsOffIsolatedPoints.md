## What changed

Proved `AlgebraicGeometry.exists_etale_splits_off_isolated_points` in
`Sheaf.AlgebraicGeometry.EtaleSplitsOffIsolatedPoints` without changing its signature,
visibility, definitions, or public imports. Added a proof-only import of
`Mathlib.AlgebraicGeometry.Morphisms.Proper` and one fully proved private shrinking helper.
Repaired the return by deleting `elementary_pullback_point_unique` and directly using
the existing `AlgebraicGeometry.pullback_point_unique` from
`Sheaf.AlgebraicGeometry.FinitePiecePersistence`. Its private visibility is accessed
with a proof-only `import all`; no dependency module or interface is changed.

The proof applies the existing elementary multiple-point theorem, proves finite open
pieces closed using properness over a separated base, deletes the closed images of
pairwise intersections, and invokes finite-piece persistence. It constructs the open
complement explicitly and proves its avoidance clause using the residue-tensor-product
point description. Pullback symmetry and open preimage isomorphisms provide the
orientation required by the public statement. The empty family follows uniformly;
its intersection of base neighbourhoods is top and its complementary open is top.
The proof of the shrinking helper follows the already formalized closed-image pattern
in `FiniteUnramifiedNeighbourhoodsDisjointRefinement`, without importing that module
or its unrelated unramified theory.

Updated the existing node's proof, proof dependencies and proof origin to match the
implementation. The source Stacks Tag 02LN was checked on its official webpage;
the local literature source is absent on this machine. Semantic LeanFinder, Loogle
and source searches confirmed that Mathlib's Zariski-main splitting theorem is weaker.
The unit `sk-thm-p1` and all of its realized steps remain unchanged.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.exists_etale_splits_off_isolated_points`
(node `lem-weil-pbc-etale-splits-off-isolated-points-technical`). No holes added;
no `sorry` remains in the delivered module. The private helper
`disjoint_finite_pieces_after_shrinking` is proved. The duplicate
`elementary_pullback_point_unique` helper was removed in this repair; point uniqueness
is now supplied by the existing proved theorem `AlgebraicGeometry.pullback_point_unique`.
The proof continues to use the existing elementary-neighbourhood and persistence
modules; their lower dependencies are not part of this delivery. The second reader checked the
full axiom closure: the theorem and helper use only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed the duplicate local point-uniqueness theorem
`AlgebraicGeometry.elementary_pullback_point_unique`; reuse of
`FinitePiecePersistence` replaces it without any new node or import dependency.

Removed proof dependency `lem-weil-pbc-proper-immersion-closed`: only the closed
range of a proper inclusion is needed, not a closed-immersion structure. No import
was removed: both original proof-only imports are used, and the original public
imports are retained for the unchanged interface. No other nodes or modules of the
original route were pruned. No global unreachability claim is made for the removed
node, which other consumers may still need.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified that `elementary_pullback_point_unique`
duplicated `AlgebraicGeometry.pullback_point_unique` word for word. The repaired proof
imports and uses that existing theorem, with `import all` to access its private name.
No false statement or interface problem was found. The earlier proof plan's
closed-immersion upgrade was unnecessary. The multiple-point lemma returns
`pullback f φ`, whereas this theorem specifies `pullback φ f`; the proof transports
the entire decomposition through Mathlib's pullback symmetry. No forced adaptations
or new nodes are needed.


## Second reading by R1

1. **Interface unchanged — pass.** Read the whole delivered module and its repository
   diff. The signature of `exists_etale_splits_off_isolated_points` is byte for byte
   identical, including both typeclass hypotheses, injectivity, isolation, the elementary
   residue-field condition, and every decomposition and avoidance clause. No definition
   or public import changed. `import all FinitePiecePersistence` remains proof-only.
2. **Proof and axioms — pass.** Compiled with `lcompile.py` without errors or warnings.
   Compiled a scratch copy with `#print axioms` for the main theorem and private shrinking
   helper: both list exactly `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
   Scanned the delivered sources for sorry, axiom, unsafe, opaque, implemented_by and
   extern: none. All opens and base restrictions are explicit constructions; the chosen
   marked points occur only within theorem proofs, with no definition choosing data from
   an unproved existence theorem.
3. **Split-off statements and duplication — pass.** No new sorry theorem or node is
   delivered. Read the private helper: separatedness makes the inclusions proper,
   finiteness makes their pairwise-intersection images closed, uniqueness and injectivity
   make these images avoid t, and persistence supplies the retained marked points.
   For n=0 the base intersection and W are top; for n=1 no off-diagonal image is deleted.
   Read the existing proved `pullback_point_unique` and checked its projections and
   residue-isomorphism hypothesis at the avoidance call. The deleted duplicate is absent.
   Searched Mathlib with msearch grep `isCompl|finite.*isClosed|isClosed.*finite|
   of_comp_of_isSeparated` and searched upstream and Sheaf for isolated-point splitting
   and pullback uniqueness. The nearby disjoint-refinement theorem requires unramified
   pieces and yields closed immersions, so it cannot replace this helper for general
   finite pieces.
4. **Route, imports and pruning — pass.** Read the official Stacks 02LN statement and
   proof at https://stacks.math.columbia.edu/tag/02LN. Local finite type supplies the
   multiple-point theorem, separatedness supplies proper inclusions, distinctness is
   used only to avoid intersection images, and the elementary residue isomorphism
   supplies avoidance. Pullback symmetry transports each conclusion with explicit
   open preimage isomorphisms. Mathlib's Zariski-main theorem (read lines 47–53) lacks
   the elementary residue and uniqueness conclusions. Both Sheaf imports are used;
   Proper supplies `IsProper.of_comp` and finite-to-proper instances. Public imports
   support the unchanged interface. Compared old/new proof_deps: precisely
   `lem-weil-pbc-proper-immersion-closed` is removed and is reported above. Read
   `dag/units/sk-thm-p1.json`, including realized: the pruned technical lemma realizes
   no unit step, and no unit statement or route is bypassed.
5. **Node agreement — pass after documentation repairs.** Only proof, proof_deps and
   proof_origin differ in the existing node. The dependency set equals the union of
   step uses. Read the Lean/Mathlib records for all dependencies: they supply the
   multiple-point neighbourhood, separated base change, proper finite maps, proper
   inclusions, persistence, etale composition and the fibre-product point description.
   The final node step explicitly records reuse through import all and transport by
   pullback symmetry. No new-node requirements apply.

Second reading changed documentation only: corrected the theorem docstring to describe
uniform use of the multiple-point theorem at n=0 and closed ranges of proper inclusions
instead of the pruned closed-immersion upgrade. Changed the node's union index to i≠j
rather than i<j to mirror the construction exactly, and recorded the full axiom closure.
The Lean proof needed no repair. Closed one original hole; added zero holes.
