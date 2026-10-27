## Worker report

The module `Sheaf.AlgebraicTopology.CubicalSignedCoordinateHomotopy` supplies the
actual signed coordinate paths and states
`IntegralLatticeCubical.signedCoordinateHomotopy`, with one `sorry` and the full
seven-step natural-language proof in its docstring. All four helper definitions
have actual data, with no postponed well-definedness obligation. No node statement,
proof, dependency list or source is changed; only the item's `lean` is set.

Source read: the complete node statement and its seven proof steps; Stacks
`more-algebra.tex`, the alternating differential immediately before
`definition-koszul-complex` (Tag 0623); and the current blueprint
`latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` direct-images
proof, paragraph (3). The Stacks source is comparison only and the current
blueprint supplies the route location. The coordinate calculation is explicitly
agent-written, exactly as the node records; it is not attributed to Stacks.

Hypotheses and clauses, in order:

- Nonnegative integer rank is `r : ℕ`. The lattice is `Fin r → ℤ`; its ordered
  standard basis is the existing `unitVector r i`. Index `i : Fin r` represents
  the node's indices 1 through r by the order-preserving shift of one. Both
  membership and the strict-order sign counts are preserved by this shift.
- `Directions r a` is the existing subtype of finite subsets of `Fin r` with
  integer cardinality exactly `a : ℤ`. `Chains r a` is the existing finitely
  supported integer functions on pairs `(v,I)`, with distinguished generators
  `cell r a v I`. This is the free abelian group of the node, not an arbitrary
  module assumed to be free. Outside the stated range its index is empty, so
  it is the zero group. The existing `cell` is zero for a mismatched degree.
- The differential is the existing `boundary r a`: `Finsupp.linearCombination`
  of the sum over `i ∈ I`, with coefficient
  `(-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card` and difference of the translated
  and untranslated cells on `I.erase i`. This is exactly the displayed
  differential and the node's `q_i(I)`. The theorem's second conjunct explicitly
  states `a ≤ 0 → boundary r a = 0`. There are no directions in degree zero and
  no cells in a negative degree.
- `resetCoordinate r i v` is literally `v - v i • unitVector r i`.
  `coordinateProjection r i a` is the unique linear extension of zero when
  `i ∈ I`, and the reset cell otherwise. The fifth conjunct states that basis
  formula, and the third states the zero map outside the rank range.
- `signedCoordinateSum` is defined for `{A : Type u} [AddCommGroup A]`, for any
  explicitly declared universe `u`. For `0 < n` it sums over integer `Ico 0 n`;
  for `n = 0` it is zero; otherwise it is the negative sum over integer `Ico n 0`.
  These are precisely the three cases in the node, including the endpoints.
- The first conjunct universally quantifies the coefficient group, family
  `b : ℤ → A`, and every integer `n`, and gives both identities verbatim:
  the signed sum of `b(k+1)-b(k)` is `b(n)-b(0)`, and the difference of the
  sums at `n+1` and `n` is `b(n)`. No order, divisibility, finiteness or
  nontriviality condition is imposed on the group.
- `coordinateHomotopy r i a` is a genuine integer linear map, defined by
  `Finsupp.linearCombination`. Its value is zero when `i ∈ I`; otherwise it
  multiplies the signed sum at `v i` by the same alternating sign as the node.
  The summand is the cell at `resetCoordinate r i v + k • unitVector r i` on
  `insert i I`. The sixth conjunct states this exact basis formula, using
  `I : Directions r a`, so no out-of-degree generator is smuggled in.
  The fourth conjunct explicitly states zero in top degree and outside the
  complete integer degree range. Being a linear map supplies the required
  homomorphism extension; integer linearity is equivalent to additivity for
  these abelian groups and imposes no additional hypothesis.
- The seventh conjunct is equality of linear maps in every degree `a : ℤ`:
  `incomingBoundary.comp coordinateHomotopy` plus the transported
  `coordinateHomotopy (a-1).comp boundary` equals `LinearMap.id` minus the
  coordinate projection. `incomingBoundary` is the published differential
  from `a+1` transported to `a`. `LinearEquiv.cast ... (sub_add_cancel a 1)`
  transports `(a-1)+1` to `a` in the other term; it changes no basis data.
- The last conjunct evaluates that left side on every generator. It is the
  original cell when `i ∈ I`, and the original cell minus its reset otherwise.
  There is no restriction on `v i`, on its sign, or on `a`. No translation
  equivariance clause appears anywhere.

Dependency declarations read and used:

- The sole statement/proof dependency `def-weil-pbc-free-module` records
  `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`. Its full class and
  basis docstring were read, including `Module.free_iff_set`. That module is
  imported directly. Mathlib's `Finsupp.linearCombination` in
  `Mathlib.LinearAlgebra.Finsupp.LinearCombination` realizes the required unique
  finite expansion and linear extension, rather than duplicating freeness.
- The already published module
  `Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction` provides
  `IntegralLatticeCubical.Directions`, `Chains`, `cell`, `unitVector`, `boundary`
  and `incomingBoundary`. Every signature, definition and docstring was read,
  also from current server source with `scompile.py --source`. These are
  reused unchanged; the downstream proposition `contraction` is never used.
  They are definitions of the objects already in this node, not an assumption
  of the parent's result. No second cubical chain or boundary definition is made.
- `Mathlib.Data.Int.Interval` supplies finite integer intervals used in the
  signed-sum definition. `Finsupp.linearCombination` and `LinearEquiv.cast`
  are available through the published chain module's public imports.

Import-cycle notice for maintenance: the parent's DAG proof lists this lemma.
Adding a proof import from `IntegralLatticeCubicalContraction` back into this
module would close an import cycle, since this statement reuses the parent's
published definitions. That proof import is to be omitted under
`stages/2-statements.md` section 3 rule 7. This delivery does not add a logical
DAG edge to the parent proposition or change the parent. Extracting its shared
chain definitions is a subsequent library organization task for stage 3.

Edge cases checked before delivery:

- `r = 0`: `Fin r` is empty, so all coordinate claims are vacuous. The generic
  signed-sum identities are still asserted. The only chain basis is the vertex
  at the unique lattice point in degree zero.
- Empty direction set: outgoing boundary is the empty sum and the surviving
  incoming face is the signed-path telescope. Top degree: every direction set
  contains `i`, so homotopy is zero, while homotopy after boundary is the cell.
- `v_i = -1`: the signed sum is minus the single term at `-1`; in the case
  containing `i`, the two sums give zero minus this negative term. `v_i = 0`:
  the path itself vanishes, but the containing-`i` boundary gives the single
  term from the sum at 1. Both produce the original cell as required.
- Negative degrees and degrees above r have no direction subsets. This also
  handles the adjacent degrees `-1` and `r+1`; the degree casts are equality
  transports only and never restrict the quantified integer degree.
- Independent finite arithmetic check, using integer-valued finitely supported
  chains: all 3,210 basis equations in ranks 0 through 3 with vertex coordinates
  from -2 through 2 passed, including all direction subsets and all coordinates.
  Top-degree homotopy vanishing was checked in the same calculation. Both
  signed-sum identities passed for `n = -8,...,8` on constant, linear,
  quadratic and alternating integer families. This supports the sign and edge
  case audit; the Lean proof remains `sorry` as required for stage 2.

Searches for existing notions/statements:

- `msearch.py leanfinder`, query “Signed coordinate paths in integer lattice
  cubical chains give d H plus H d equal to identity minus coordinate collapse”:
  eight hits, Dold-Kan projection decompositions and simplicial homotopies.
  These use simplicial degeneracies, not the coordinate-path formula; no match.
- `msearch.py loogle`, query `"sum", "Ico"`: twelve hits, including interval
  reindexing and sum endpoint formulas. They do not define this oriented
  integer path or state the cubical identity; no exact match.
- `msearch.py leansearch`, query “Sum over oriented integer interval from zero
  to n has difference b n under n to n plus one”: eight hits including
  `Finset.sum_range_succ_sub_sum`, `sum_Ico_eq_sub`, and interval endpoint
  formulas. These supply ordinary interval tools but no complete signed-path
  construction in integer degrees and no coordinate homotopy.
- `msearch.py grep`, query `cubical|coordinate.*[Hh]omotopy|signed.*[Ss]um`:
  twelve unrelated hits (incenters, characteristic-polynomial coefficients,
  and `Data.Sign` sign choices); no matching construction.
- `rg` in project `lean/Sheaf` found the published integral cubical chain,
  diagonal and partition modules, which were opened. The chain definitions
  are reused. No signed coordinate homotopy or coordinate-reset declaration
  was present. `rg` in `lean/WeilConjectures` and the required node-id search
  there found no match. Additional name searches for `signedCoordinateSum`,
  `resetCoordinate`, `coordinateProjection`, `coordinateHomotopy` and
  `signedCoordinateHomotopy` in the relevant project sources found no collision.
  Mathlib interval and finite-linear-combination source definitions were read.

No statement correction, new node or dependency repair is needed: the four
helpers are the explicit coordinate-path data owned by this very lemma, as
permitted by the human's helper-construction instruction. There is no
STATEMENT-DISPUTED finding. The first `scompile.py` run passed for the full
module; final validation follows the direct dependency import adjustment.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
