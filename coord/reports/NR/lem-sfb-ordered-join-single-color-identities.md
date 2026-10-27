## Worker report

The module `Sheaf.AlgebraicTopology.OrderedJoinSingleColorIdentities` states
`AlgebraicTopology.OrderedJoin.singleColorIdentities`, with its only proof `sorry`.
It states both identities in the node for every integer degree. No definitions,
additional axioms, new nodes, dependency repairs, or statement corrections are introduced.

Hypothesis and clause correspondence (namespace `AlgebraicTopology.OrderedJoin`):

- The integer r >= 1 and colors I = {0,...,r-1} are `(r : ℕ) (hr : 1 ≤ r)` and
  `Fin r`. The arbitrary sets and their specified vertices are
  `(X : Fin r → Type u)` and `(v : ∀ i : Fin r, X i)`. The universe `u` is explicit
  and unrestricted. There is no decidable-equality or finiteness assumption on X.
- An ordered distinct-color symbol is the existing `Symbol X q`: its underlying
  `Face X` has a finite color set and a vertex for each member, with
  `(colors.card : ℤ) = q + 1`. Increasing color order uniquely orders its vertices;
  this is precisely the node's sequence representation, with no quotient of vertices.
- The specified free integer module is the existing `Chain X q = Symbol X q →₀ ℤ`.
  Its specified basis is `Finsupp.basisSingleOne`, the Mathlib `Module.Basis` notion
  underlying `Module.Free` in the recorded dependency. This is the concrete standard
  model of the free abelian group on the displayed symbols, not an additional
  hypothesis on arbitrary modules. Its basis is present in the imported constructions.
- For q=-1, cardinality zero forces the unique empty face (the vertex function has
  empty domain), so the chain group is the free integer module on the empty symbol.
  For q<-1 the cardinality equation is impossible; for q>=r it would exceed the
  cardinality of `Fin r`. These are the node's zero groups, represented as Finsupp
  on an empty symbol type. No endpoint is removed from the quantified identities.
- The node's d is `boundary X q (q-1)`. Its actual definition is the linear extension
  of the sum over present colors of `positionSign colors i • symbolTerm ... (erase ...)`.
  The sign counts earlier colors, exactly zero-based position. A singleton deletes
  to the empty symbol with coefficient 1; the empty sum gives d at -1 equal to zero.
- Its c_i is `insertion v i q (q+1)`. Its actual definition is zero for a present
  color, otherwise the chosen inserted face with sign `positionSign colors i`.
  The map does not examine any vertex equality. The two degree arguments allow
  endpoints to be given without casts between arithmetic expressions for integers.
- Its R_i is `remainder v i q`, zero for an absent color and otherwise the original
  symbol minus `replaceColors v {i}` of that symbol. This replacement is precisely
  T_i. The actual basis assignments extend by `Finsupp.linearCombination ℤ`.
  `symbolTerm` returns zero for a face of incorrect target cardinality, and Finsupp
  on an empty symbol type is the zero module, so all requested zero components agree.
- The first conclusion is the first conjunct
  `∀ q : ℤ, (boundary X (q - 1) (q - 2)).comp (boundary X q (q - 1)) = 0`.
  It gives d_{q-1} d_q = 0 in every integer degree. Comp takes its right argument first.
- The second conjunct quantifies both `(q : ℤ)` and `(i : Fin r)` and equates
  `(boundary X (q+1) q).comp (insertion v i q (q+1)) +
  (insertion v i (q-1) q).comp (boundary X q (q-1))`
  with `LinearMap.id - remainder v i q`. These are exactly d c_i + c_i d = id - R_i.
- The final node clause about -1, r-1, and the outside zero degrees is rendered by
  the unrestricted `q : ℤ`, with the concrete group definitions just described.
  No relation at all between original vertices and chosen vertices is assumed.

Dependencies read and used:

- Recorded stmt_deps/proof_deps node `def-weil-pbc-free-module`:
  `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`. Its full class signature
  and docstring were read: freeness is existence of an indexed `Module.Basis`.
  The concrete specified basis here is the already imported
  `Mathlib.LinearAlgebra.Finsupp.VectorSpace`, `Finsupp.basisSingleOne`, and maps are
  extended by `Mathlib.LinearAlgebra.Finsupp.LinearCombination`,
  `Finsupp.linearCombination`. No private copy of the free-module notion is made.
- Public import `Sheaf.AlgebraicTopology.OrderedJoinPartialContraction`: read its full
  source and the parent node's declaration record. Reuse its existing `Face`, `Symbol`,
  `Chain`, `symbolTerm`, `erase`, `replaceColors`, `insert`, `positionSign`, `boundary`,
  `insertion`, and `remainder`, with the full definitions and docstrings as published.
  The parent theorem `partialContraction` is not used by the statement or its proof plan.

Import-cycle exception: `lem-sfb-ordered-join-partial-contraction` already owns the
explicit construction declarations and names this item in its proof_deps. This item
therefore imports its data module. The reverse proof-only import into that parent must
be omitted under stages/2-statements.md §3.7, otherwise it creates an import cycle.
The parent is not added as a DAG stmt_dep (which would likewise create a cycle).
The constructions are reused as already published, rather than duplicated or silently
replaced. The proof docstring uses only the free-basis formulas and elementary sign
cancellation, never the downstream partial contraction theorem.

Source check: opened the current `literature/blueprint/latest/blueprint/
sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md`. Paragraph (3) concerns compactification;
as the node explicitly records, this ordered-join calculation is an agent expansion,
not a claim made in the blueprint. The new docstrings retain that distinction and
carry all five proof steps from the accepted split, including their sign calculations.

Edge cases checked before delivery: r=1; q=-1 and the empty face; q=0 and augmentation;
q=r-1 and zero top insertion; q<-1 and q>=r and the empty symbol types; a present
vertex both equal and unequal to the chosen vertex. Independently evaluated the actual
basis formulas with finite integer counters for r=1,...,4 and X_i={0,1,2}, v_i=0.
Both identities passed on all 1,252 symbol/color pairs, including empty/top faces.
No assumption excludes coincident chosen vertices or infinite X_i. No dispute found.

Searches actually made (2026-10-24):

- msearch.py leanfinder: "On augmented free abelian chains of ordered distinct-color
  simplices, signed vertex insertion satisfies d c plus c d equals identity minus
  vertex replacement". Eight hits, including Rep.standardComplex.d_of,
  Rep.barComplex.d_single and simplex-category insertion relations. None states these
  two identities for the ordered distinct-color augmented chains.
- msearch.py loogle: "Finsupp.linearCombination, Finsupp.basisSingleOne". Zero hits;
  the separate Mathlib sources provide the standard construction and basis, not this
  particular theorem.
- msearch.py grep in AlgebraicTopology:
  `(join|colored|coloured).*(boundary|insert)|(boundary|insert).*(join|colored|coloured)`.
  Zero hits.
- msearch.py leansearch: "Signed insertion on augmented ordered colored join chains
  is a chain homotopy from vertex replacement to the identity". Eight hits, generic
  Homotopy API and DoldKan.homotopyPToId. None is the stated concrete identity.
- rg in lean/Sheaf and lean/WeilConjectures:
  `OrderedJoin|orderedJoin|ordered.join|single.color|vertex.replacement`.
  Found the existing OrderedJoinPartialContraction constructors and other consumers;
  the former states the full partial contraction, not the single-color identity.
  grep for the exact item id in lean/WeilConjectures found no declaration.
- rg in the same project trees and Mathlib for
  `singleColorIdentities|single_color_identities` found no existing name.
  rg for ordered-join in chapter definition nodes found no separate definition node
  carrying these constructors. No new independent notion was needed.

Validation: the delivered module compiled through prescribed scompile.py, both its
sandbox and final library module names, in 1.3 seconds each, with no errors or warnings.
All binders and universes are explicit; `set_option autoImplicit false` is enabled.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
