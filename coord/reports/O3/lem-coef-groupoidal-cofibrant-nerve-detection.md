## Worker report

The module `Sheaf.AlgebraicTopology.GroupoidalCofibrantNerveDetection` states
`SSet.Bergner.groupoidal_cofibrant_nerve_detection`, with its sole theorem proof
left as `sorry`. Its docstring retains all eight steps of the DAG proof. The
helper `SSet.Bergner.degreeDiagramMap` constructs the actual natural transformation
on ordinary degree categories from the given fixed-object enriched functor; it
chooses no additional map or mathematical data.

Source checked: [Dwyer–Kan, Simplicial localizations of categories](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf),
Corollary 9.6, printed p. 280, and the definitions in 1.4(iv)–(vi).
The source's fixed-object setting and both cofibrancy hypotheses are retained.

Clause-by-clause correspondence:

- A small object set is `{O : Type u}`, with the universe explicitly declared.
  `{U V : Fixed O}` are simplicial categories on precisely this common set.
  `f : U ⟶ V` is `FixedHom`, whose object function is literally the identity.
  Its mapping maps preserve identities and composition as equalities of simplicial maps.
- The fixed-object weak equivalences and fibrations are the existing
  `fixedWeakEquivalences O` and `fixedFibrations O`; these mean, respectively,
  realization-based weak equivalences and horn lifting for every mapping set.
- `hU : fixedCofibrations O (discreteInclusion U)` and its analogue `hV`
  express exactly cofibrancy: the identity-only category's canonical inclusion
  has the left lifting property against every mappingwise trivial Kan fibration.
  There is no chosen-model-structure parameter or extra fibrancy hypothesis.
- `hgroupU : ∀ (a b : O) (e : (U.Hom a b) _⦋0⦌), IsEquivalenceVertex U e`
  expresses that every morphism of the component category is invertible; likewise
  `hgroupV`. `IsEquivalenceVertex` asserts the existence of a reverse vertex whose
  two composites equal the respective identity in Mathlib's simplicial component
  quotient. Every component has a vertex representative, even without Kan
  fibrancy, so this is equivalent to the stated component-groupoid hypothesis.
- `degreeDiagram U` has the ordinary category of degree-q arrows in degree q.
  Its degreewise nerve consists of all composable p-arrow strings, canonically
  the displayed coproduct over object strings of products of mapping simplices.
  Nerve faces compose or omit arrows and degeneracies insert identities. The
  diagram maps apply the mapping-set operators and fix objects. Thus the existing
  `TwoSidedSimplicialGrothendieck.diagonalNerve` is exactly the node's diagonal
  classifying nerve; length-zero strings account for empty products.
- `degreeDiagramMap f` applies `f.map a b` in each degree. The existing
  `TwoSidedSimplicialGrothendieck.diagonalNerveMap (degreeDiagramMap f)` is
  therefore the particular induced map `Nf`, rather than an arbitrary map.
- The conclusion is an `↔`: `fixedWeakEquivalences O f` on the left and
  `Enhanced.IsWeakHomotopyEquivalence` of that induced diagonal map on the right.
  No clause is replaced by one direction, contractibility, or a Kan specialization.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.SortedSimplicialAlgebraModel`:
  `AlgebraicTopology.sorted_simplicial_algebra_model`, with its full transfer
  statement, generating families and functorial factorizations. It supplies the
  sorted-theory model framework named by the node.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen` and its weak-equivalence structure;
  the statement uses the same `SSet.Enhanced.IsWeakHomotopyEquivalence`.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`:
  `SSet.Bergner.Fixed`, `FixedHom`, `bundleMap`, `IsEquivalenceVertex`,
  `fixedWeakEquivalences`, `fixedFibrations`, `discreteInclusion`,
  `fixedCofibrations`. Their data, signatures and docstrings were read.
- `Sheaf.AlgebraicTopology.CofibrantCompletionNerveEquivalence`:
  `SSet.Bergner.degreeDiagram` and its degree-category construction. Its public
  imports supply `CategoryTheory.CofibrantSimplicialInversion.degreeFunctor`
  and `CategoryTheory.TwoSidedSimplicialGrothendieck.diagonalNerveMap`; both
  constructions were read in their owning source modules. The completion theorem
  itself is not an additional assumption.

The last two already-landed nodes were added to `stmt_deps` to record the actual
shared interfaces used by the statement, as authorized by brief-stage2 §5.
Both dependency closures were checked and neither reaches this item. No new node,
dependency repair, natural-language statement change, or disputed statement is needed.
All ten recorded proof dependencies with Lean modules are imported. The nine
proof-only imports omit `public`; Kan–Quillen is also a statement dependency and
is public. Their complete eight-step proof plan is retained in the theorem docstring.

Edge cases checked: `O` empty gives empty diagonal nerves and vacuous mappingwise
conditions; disconnected object components are unrestricted; empty off-diagonal
mapping sets give vacuous vertex conditions without imposing nonemptiness. Identity
mapping sets contain their required identities. Zero nerve degree has one empty
arrow string per object, so empty products have the required singleton meaning.
Non-Kan mapping sets and nonconnected nerves are allowed by every binder. No
inhabited, connected, or Kan instance is required. Cofibrancy remains in the statement
although the saved proof plan establishes a more general detection argument.

Search evidence retained from the interrupted attempt in `searches.jsonl`:

- `msearch.py`, `grep`, query `groupoid.*(nerve|cofibrant)|nerve.*(groupoid|cofibrant)`:
  zero Mathlib hits.
- `msearch.py`, `loogle`, query `CategoryTheory.nerve, HomotopicalAlgebra.WeakEquivalence`:
  zero hits.
- `msearch.py`, `leanfinder`, query “A functor fixing objects between cofibrant
  simplicial categories with groupoidal component categories is a mappingwise weak
  homotopy equivalence if and only if its diagonal classifying nerve is a weak
  equivalence”: eight hits on model-category homotopy categories and truncated
  simplicial homotopy categories; no matching enriched detection theorem.
- `msearch.py`, `leansearch`, query “The diagonal classifying nerve detects mapping
  space weak equivalences of simplicial categories with groupoidal component
  categories”: eight general nerve/diagonal declarations, no detection theorem.
- Current `rg` searches in Mathlib's AlgebraicTopology, upstream `WeilConjectures`,
  `dag/lean_names_upstream.json`, and project `lean/Sheaf` found no matching theorem
  or declaration-name collision. Searches for the item's id in upstream found none.
  The project's existing completion theorem concerns a canonical completion map;
  the diagonal/coherent comparison theorem concerns another nerve, so neither is
  the present arbitrary-functor detection statement. Shared degree and nerve
  definitions are reused rather than reconstructed.

Recovery and verification: the required first dry run diagnosed the absent report.
The initial wrapper compile then diagnosed the unqualified `Functor.ext` resolving
incorrectly in the helper. Qualifying it as `CategoryTheory.Functor.ext` fixed
elaboration without changing the theorem statement or helper data. A subsequent
`scompile.py N3 lem-coef-groupoidal-cofibrant-nerve-detection` run compiled the
sandbox and destination-module checks cleanly, each in 1.4 seconds, without warnings.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
