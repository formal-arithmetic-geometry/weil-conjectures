## Worker report

Stage 2, Q92, 2026-10-23. The delivered module is
`Sheaf.AlgebraicTopology.ShuffleHorizontalFaceReindexing`, with main declaration
`AlgebraicTopology.ShuffleHorizontalFace.horizontal_face_reindexing`.
All eight declarations appear in `lean.declarations`. There is one postponed
theorem, whose whole proof is `sorry`; its docstring supplies the complete
eight-step counting argument. All definitions have actual data, including the
two prefix-index bounds, which use the existing sublist count inequality.

The previous worker's unchanged-item failure concerned stage 1, not a failed
Lean statement. The current node has the Q156 reviewed split, no Lean record,
and a stage-2 queue entry. The stage handoff in brief-stage2 section 0 explicitly
allows formalizing it. This delivery preserves that split and changes only
the item's `lean` field. No statement correction or dependency change is needed.

Clause-by-clause correspondence (the theorem's `a` is the shorter horizontal
degree; the node's positive horizontal degree is therefore `a + 1`):

1. A word with exactly the specified H and V counts is `Word a b`, a subtype of
   `List Bool` with `length = a + b`, `count false = a`, and `count true = b`.
   Here `false` is H and `true` is V. The redundant length equality records
   the node's `n = a + b`. This is a finite set: a fixed-length list of booleans
   is determined by its tuple of entries, and the count constraints cut out a
   subset of that finite set. The empty word is retained at `(a,b) = (0,0)`.
2. `horizontalCount w k` and `verticalCount w k` count H and V in `w.take k`,
   hence exactly the positions strictly below `k`, including `k = 0` and the
   terminal vertex. `inversions` counts pairs in the product of position ranges
   satisfying `r < s`, letter V at `r`, and letter H at `s`. `sign` is the
   corresponding integer power of minus one, with no permutation conventions.
3. The arbitrary sets are `X : Type u` and `Y : Type v`, with explicitly
   declared independent universes. The input strings are functions on
   `Fin (a + 1 + 1)` and `Fin (b + 1)` for the positive horizontal degree.
   `evaluate` lists all vertices using exactly their prefix-count input
   indices. Their bounds follow from `List.take_sublist` and `List.Sublist.count_le`;
   there is no default entry, truncation, arbitrary choice, or nonempty-type
   hypothesis. The definitions make no injectivity or distinctness assumption.
4. `HorizontalFace a b` is the labeled pair `(w,k)`, with `k <= a+b`, and the
   disjunction of the two endpoint H tests and the interior HH test.
   The Option-valued letter tests mean a nonexistent letter is never an H,
   including at the empty word. The added vertex bound is precisely the
   node's range of sequence entries, not an additional restriction.
5. `IsEmpty (HorizontalFace 0 b)` states the final zero-horizontal-degree clause.
   Every positive horizontal degree is uniquely a successor. The second
   conjunct gives `Phi : HorizontalFace (a+1) b ≃ Fin (a+2) × Word a b`.
   `Equiv` expresses bijection on labeled pairs, retaining the distinction
   between different marks even if their evaluated strings coincide.
6. In the forward clause, the first component is `horizontalCount w k`.
   The second component is `w.eraseIdx (min k (a+1+b-1))`. This removes
   position zero initially, the terminal H at the terminal endpoint, and the
   second H at position `k` in an interior HH pair. Replacing HH by H is
   literally that erasure. These clauses fix the specified forward map.
7. The inverse clause for label zero prepends `false` and marks zero. At
   label `a+1` it appends `[false]` and marks `a+1+b`. For an interior label
   it writes the shorter word as `P ++ false :: Q`, with
   `P.count false + 1 = i`, and returns `P ++ false :: false :: Q`, marked
   at `P.length + 1`. This is splitting the i-th H counted from one.
8. For each interior mark, the forward clause gives `1 <= i`, `i < a+1`,
   `k = i + verticalCount w k`, and `inversions w = inversions shorter +
   verticalCount w k`. Thus its count is the node's `t = B_k`.
   At the initial endpoint it gives label zero and equality of inversion
   counts; at the terminal endpoint it gives label `a+1` and the extra
   `b` inversions. The endpoint hypothesis itself is `k = a+1+b`.
9. The sign clause is verbatim the integer identity
   `sign w * (-1)^k = (-1)^i * sign shorter`, without reducing it to parity
   or dropping the inversion equalities.
10. The final conjunct universally quantifies both input strings and every
    marked face. `List.eraseIdx k (evaluate w x y)` is `d_k z`.
    On the right, `Fin.removeNth i x` is Mathlib's deletion of input entry i,
    and the vertical input is unchanged. The accompanying equality of
    `Finsupp.single ... (1 : Int)` expresses the identical equality as basis
    symbols in the free integral module on strings. Mathlib's `Finsupp`
    construction is used directly, not a private free module.

Dependency declarations read and used:

- `def-weil-pbc-free-module` has status `mathlib` and records
  `Module.Free` in `Mathlib.LinearAlgebra.FreeModule.Basic`. Its full
  declaration says a semiring module is free if it has a basis, with
  `exists_basis : Nonempty ((I : Type v) × Basis I R M)`. This module is
  imported publicly, and free integral basis symbols use Mathlib's
  canonical finitely supported functions and `Finsupp.single`.
- Auxiliary Mathlib APIs: `List.take_sublist`, `List.Sublist.count_le`,
  `List.ofFn`, `List.eraseIdx`, `Fin.removeNth`, and finite-set products,
  filtering, and cardinality. The `Fin.removeNth` definition and its
  docstring were read: it precomposes with `Fin.succAbove`, omitting exactly
  the indicated entry.

Searches for existing statements and constructions:

- `msearch.py`, LeanFinder: "Horizontal marked faces of shuffle words reindex
  by deleted horizontal input vertex and a shorter shuffle with inversion
  count signs". Eight hits, headed by simplex-category degeneracy normal
  forms (`standardσ_cons`, `simplicialInsert`), not this bijection or formula.
- `msearch.py`, Loogle: `"shuffle", "face"`. Zero hits.
- `msearch.py`, grep of Mathlib:
  `shuffle.*(face|word)|horizontal.*(face|inversion)`. Zero hits.
- `msearch.py`, LeanSearch: "Bijection of horizontal marked shuffle words with
  a deleted horizontal input vertex and a shorter shuffle, including endpoint
  signs". Eight hits, including set bijection restriction and permutation
  signs; none states the marked-word reindexing or the endpoint counts.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, both by item ID and by
  shuffle/word/horizontal-face names: no existing declaration of this item.
  The Sheaf module `SimplexLatticeShuffleBoundary` has a downstream theorem
  whose proof requires this item. Its `LatticePath` is a monotone function
  into a product of finite ordinals, not a list of H/V letters. It supplies
  neither the marked-word bijection nor its inverse or inversion formulas.
  Importing it would make the proof dependency cyclic. The present helpers
  introduce exactly the literal word notation already in this item's text;
  they do not reproduce that chain complex, path sum, or boundary theorem.
- `rg` of Mathlib's list files and the project for `IsShuffle`,
  `IsInterleav`, and shuffle/interleaving definitions: no existing word
  definition. Existing list counts, finite tuples, and erasure are reused.
- `tools/blueprint_refs.py search shuffle`: zero imported blueprint matches.
  The ancestor command reports `None`, as already recorded by the item's
  inherited `blueprint.from`; that field is preserved. No new node needs it.

Source and edge cases:

The current `literature/blueprint/latest` direct-images proof was read. Its
paragraph (3) discusses proper and open direct images and compactification;
it does not assert this combinatorial statement. Accordingly the module
attributes its counting argument to the agent-written DAG proof, not to
that paragraph or to the unavailable Weibel reference. The node's source
and its existing explicit attribution are unchanged.

Before writing the statement, I checked the single-H and no-V cases by
the forward/inverse descriptions. After compilation I exhaustively
enumerated all words for `0 <= a,b <= 4`, covering 545 labeled horizontal
faces. For each, the check verified uniqueness and surjectivity onto
`{0,...,a} × W_(a-1,b)`, the word collapse and all three inverse rules,
interior and endpoint inversion counts, all signs, and the evaluated
deletion identity with both distinct and constant (fully repeated) inputs.
It also checked that horizontal degree zero has no labeled face, including
the empty word, and that the shorter empty word occurs correctly at `(1,0)`.
Empty X or Y impose no extra hypothesis: their positive-length input strings
simply have no inhabitants. Unequal universe levels for X and Y are allowed.

No `STATEMENT-DISPUTED` issue or node fault was found. There are no new
nodes or dependency modules. The node changes only in `lean`, and the
recorded signature was extracted verbatim from the delivered theorem.

Validation: `scompile.py Q92 lem-sfb-shuffle-horizontal-face-reindexing`
compiled the module in sandbox and library modes on the server, each in
1.1 seconds, with no errors or warnings. The `deliver2.py --no-push` dry run
passed the current server preflight and compilation (commit `a43f67b4f0b`),
with exactly the module, node, and worker report staged. A report typography
fix is included in the final packet. The worker delivers directly; the
maintainer supplies the independent review, as the current brief requires.

## Second reading by Q92

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
