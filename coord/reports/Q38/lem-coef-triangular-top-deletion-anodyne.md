## Worker report

The module `Sheaf.AlgebraicTopology.TriangularTopDeletionAnodyne` states
`SSet.Enhanced.triangular_top_deletion_anodyne`, with the sole theorem proof `sorry`.
Four concrete helper definitions introduce this node's deleted subcomplex, exact marking,
intersection and canonical marked inclusion. No theorem is proved, no object is chosen
from existence, and no existing interval category, boundary or marking API is copied.
The natural-language proof docstring follows all nine DAG proof steps, including the
involutive matching, the dimension/lexicographic rank, every horn and low-dimensional
marking case, triangle cancellation, and exhaustion.

Clause-by-clause correspondence:

- The integer `n ≥ 1` is `(n : ℕ) (hn : 1 ≤ n)`; this ranges over exactly the
  nonnegative integers satisfying the stated lower bound. All helpers are also defined
  for `n = 0`, without asserting the theorem outside its domain.
- Ordinary nerves and simplices use the Mathlib primitives publicly imported through
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, as that dependency's module explicitly
  specifies. Its `SSet.Enhanced.fullSubcomplex` constructs full vertex subcomplexes.
- `T_n` is the existing `SSet.Enhanced.TerminalComparisonArrow n`: `source` and `target`
  lie in `Fin (n+1)` and `le` requires the first to be at most the second. Its category
  has exactly one morphism when `source ≤ source'` and `target' ≤ target`, expressed
  by the two `PLift` inequality fields of `TerminalComparisonSquare`; the objects'
  own inequalities supply the middle `source' ≤ target'`. This is the stated poset,
  even though its existing Lean interface is a thin category rather than a
  `PartialOrder` instance. `terminalComparisonIndex.{u} n` is its ordinary nerve,
  degreewise lifted with `SSet.uliftFunctor.{u,0}` to arbitrary input universe `u`.
- `T_F` and `N(T_F)` are the existing `terminalComparisonFacePredicate` and
  `terminalComparisonFace`: both endpoints of every vertex must belong to `F`.
  Because `Fin (n+1)` is finite, quantifying over its finite subsets covers every
  subset. `terminalComparisonBoundary n` is precisely the supremum of these full
  nerves for proper `F`; the `F = Finset.univ` summand is bottom. Thus this reuses
  the exact `B_n`, including the empty-subset contribution.
- `Q_n` deletes exactly `(n,n)`: `triangularTopDeletion n` is the full subcomplex of
  `terminalComparisonIndex n` on vertices unequal to
  `terminalComparisonDiagonal n (Fin.last n)`. Full subcomplexes of ordinary nerves
  are the ordinary nerves of full subcategories, so its `toSSet` is exactly `Y_n`.
- `D_n = B_n ∩ Y_n` is `triangularTopDeletionBoundary n`, defined as the preimage
  of `terminalComparisonBoundary n` along `(triangularTopDeletion n).ι`. Preimage
  along the literal inclusion is exactly the intersection, regarded inside `Y_n`.
- In `triangularTopDeletionMarked n`, an edge is marked if and only if
  `(e.val.down.obj 0).source = (e.val.down.obj 1).source`. Here `val` forgets the
  deleted-subcomplex membership proof, `down` removes only the degreewise universe
  lift, and `obj 0`, `obj 1` are the endpoints of its ordinary nerve arrow.
  There is no extra alternative marking predicate. Degenerate edges have identical
  endpoints; the required structural proof is definitionally `rfl`.
- `triangularTopDeletionInclusion n` is the existing `Marked.inducedMarkingMap`
  for `(triangularTopDeletionBoundary n).ι`, so its source has exactly the induced
  marking and its underlying morphism is the canonical inclusion, not an arbitrary
  map or a chosen existence witness.
- The conclusion is exactly `Marked.markedAnodyne
  (triangularTopDeletionInclusion.{u} n)`, using the class of the named dependency.
  No fibration, quasicategory, extra finiteness or nonemptiness hypothesis is imposed.

Recorded dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.fullSubcomplex`, and
  its explicitly documented use of Mathlib `CategoryTheory.nerve`, standard simplices
  and horns. The main declaration `SSet.Enhanced.coneCategory` is a different
  component of this multi-declaration definition node and is not needed here.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`:
  `SSet.Marked.inducedMarking`, `inducedMarkingMap`, and `markedAnodyne`. The four
  generators and saturation were read in full, and the full signature of
  `marked_anodyne_lifting_calculus` was checked; its theorem is a proof input,
  not an additional hypothesis in the statement.
- Proof-only import `Sheaf.AlgebraicTopology.MarkedTriangleCancellation`:
  `SSet.Marked.marked_triangle_cancellation`. Its `markedAnodyneClass` has the
  same intended four families and closure as `markedAnodyne`; their bridge belongs
  to the future proof, not to a new assumption in this statement.
- Existing concrete helpers from
  `Sheaf.CategoryTheory.TerminalComparisonCoherence`:
  `SSet.Enhanced.TerminalComparisonArrow`, `TerminalComparisonSquare`,
  `terminalComparisonCategory`, `terminalComparisonIndex`,
  `terminalComparisonVertex`, `terminalComparisonDiagonal`,
  `terminalComparisonFacePredicate`, `terminalComparisonFace`, and
  `terminalComparisonBoundary`. Their definitions and docstrings were read in the
  local source and checked against the current source returned by
  `scompile.py --source Sheaf.CategoryTheory.TerminalComparisonCoherence`.

Import-layout issue reported for the maintainer: those existing interval definitions
are currently housed in the module of a mathematical consumer of this lemma.
This delivery imports that module to obey one definition per notion and uses only
its concrete definitions, never `terminal_comparison_coherence` or any of its
assertions. The DAG dependency lists are unchanged: adding a reverse dependency on
that consumer theorem would be a false logical dependency and a cycle. The current
module graph is acyclic and compiles. Under stage 2 §3(7), the future proof-only
import of this new module into `TerminalComparisonCoherence` must be omitted while
it would close that import cycle. Extracting its shared interval definitions into a
foundational module is a future maintainer refactor; no live file was changed here.
This is an import-layout issue, not a disputed mathematical statement.

Edge cases checked:

- For `n = 1`, `Q_1` has `(0,0)` and `(0,1)` with the single nonidentity edge
  `(0,1) → (0,0)`. The boundary intersection is the target vertex `(0,0)`.
  The edge has constant first coordinate and is marked, so the inclusion is the
  one-dimensional final marked horn, with no unintended vertex added to the source.
- For `n = 2`, the five vertices of `Q_2` are `(0,0)`, `(0,1)`, `(0,2)`,
  `(1,1)`, `(1,2)`. All five lie in `D_2`, since each vertex has at most two
  endpoints. The omitted full-support simplices include both kinds of corners
  and the constant-first triangle `(0,2) → (0,1) → (0,0)`, the latter requiring
  exactly the initial-edge triangle cancellation in proof step 8. No constant-first
  marking is lost, and no changing-first edge is marked.
- At `n = 0`, deletion removes the only vertex, so `Y_0` and `D_0` are empty.
  The helpers still make sense; the theorem correctly retains `1 ≤ n`.
- The empty proper subset contributes the empty nerve. Degenerate simplices and
  edges remain in the full subcomplexes, and all degenerate edges are marked.
- Arbitrary universe `u` is explicitly bound; the finite nerve is lifted to `u`.
  There is no equality between independent universes, and no auto-bound implicit.

Searches for an existing statement, all performed before writing the module:

- `msearch.py leanfinder`, query “The nerve of the finite interval poset minus its
  last diagonal vertex has marked anodyne proper face union, marking constant first
  coordinate edges”: eight hits, ordinary horns, nerve degeneracy, and horn-face maps;
  none states the marked interval-poset assertion.
- `msearch.py loogle`, query `SSet.anodyneExtensions, CategoryTheory.nerve`: zero hits.
- `msearch.py grep`, query
  `marked.anodyne|anodyne.*marked|interval.*poset|TwistedArrow`, restricted to
  Mathlib `AlgebraicTopology`: zero hits.
- `msearch.py leansearch`, query “The proper face union in the nerve of a finite
  interval poset with the last diagonal removed is marked anodyne”: eight hits,
  ordinary horns, strict-Segal and nerve nondegeneracy facts; none is this statement.
- `rg` of `triangular|intervalPoset|TopDeletion|topDeletion|IntervalPoset` over
  upstream `WeilConjectures` and project `lean/Sheaf` found unrelated triangular
  algebra and the consumer's interval definitions; the latter are reused.
- `grep -rn` of this node id over upstream `WeilConjectures` returned no match.
  `rg` of the chosen helper and theorem names over project, upstream and Mathlib
  returned no declarations. The upstream-name index has unrelated triangular
  field-model entries, with no declaration for this lemma.
- Read Mathlib's ordinary nerve implementation and subcomplex preimage/inclusion
  interfaces, confirming that they supply the required ordinary constructions.

Validation: `scompile.py Q38 lem-coef-triangular-top-deletion-anodyne` compiled the
file in both sandbox and library-path contexts, also compiling the missing side overlay
for `TerminalComparisonCoherence`. Both contexts finished cleanly, with no warnings.
Only the node's `lean` field changes. There are no new nodes, dependency-record
repairs, statement corrections or `STATEMENT-DISPUTED` flags.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
