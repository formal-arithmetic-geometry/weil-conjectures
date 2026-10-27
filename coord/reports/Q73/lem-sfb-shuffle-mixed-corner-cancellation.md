## Worker report

States `AlgebraicTopology.ShuffleMixedCorner.mixed_corner_cancellation` in
`Sheaf.AlgebraicTopology.ShuffleMixedCornerCancellation`. Its only proof is `sorry`.
`MixedCorner` is a real subtype definition, with no postponed data or proof.

I read the current item and its six accepted proof steps, its statement dependency
`def-weil-pbc-free-module`, and both Mathlib proof leaves. The node has no Lean record
or released repair note. The previous worker's stage-1 unchanged-node refusal does not
apply to this stage-2 statement assignment, as the current brief's stage handoff explains.
The accepted statement and split are preserved. The sole additional statement dependency is now the definition node
`def-sfb-shuffle-word-combinatorics`, recording the six existing definitions in the
landed horizontal-face module. The horizontal-face theorem is neither a statement
dependency nor a proof dependency. There are no dependency modules, statement
corrections, or disputed claims.

Source read: latest blueprint,
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3). It states the direct-image application, not this combinatorial input.
The DAG correctly calls the input agent-written; the proof docstring reproduces its six
steps rather than claiming that the blueprint itself supplies the calculation. The
requested Weibel reference is unavailable locally.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Arbitrary nonnegative a,b and n=a+b | `(a b : ℕ)` and the explicit term `a + b` throughout. |
| W with a H and b V letters | Existing `ShuffleHorizontalFace.Word a b`: a list of booleans of length a+b, with count false=a and count true=b; false=H, true=V. |
| A_k, B_k | Existing `horizontalCount` and `verticalCount`, counts of the first k letters. |
| I(w) and s(w)=(-1)^I(w) | Existing `inversions` counts ordered VH pairs; existing `sign` is its integral power of -1. |
| Arbitrary sets X,Y and sequences of lengths a+1,b+1 | Separate universes `X : Type u`, `Y : Type v`, with `x : Fin (a+1) → X` and `y : Fin (b+1) → Y`. No nonemptiness, order, injectivity, or decidable equality of X,Y is assumed. |
| Evaluated path z and deletion d_k | Existing `evaluate w x y : List (X × Y)` has exactly a+b+1 entries; `.eraseIdx k` deletes the kth entry. Every corner satisfies k<n, so all deleted strings have length n. |
| Free integral module and its basis strings | `List (X × Y) →₀ ℤ`, with `Finsupp.single string (1 : ℤ)` as the basis symbol. All terms lie in the length-n summand. Its injection into the free module on all lists is injective, so zero here is equivalent to zero in the free module on length-n strings. |
| Permutation listing H positions increasingly, then V increasingly | For each w the existential `π : Equiv.Perm (Fin (a+b))` has `List.ofFn π` equal to the concatenation of the two filtered `List.finRange` lists. This completely determines π and asserts its bijectivity. |
| Permutation inversion count is I(w) | The cardinality of the filtered finite set of pairs with `ij.1 < ij.2 ∧ π ij.2 < π ij.1` equals `inversions w`. |
| Permutation sign is s(w) | `(π.sign : ℤ) = sign w`; Mathlib's integer unit sign is coerced to ℤ. |
| n>0 | `0 < a+b →` governs the mixed-corner involution and sum. The permutation assertion also includes n=0, as the node does. |
| M={(w,k):0<k<n, neighboring letters different} | `MixedCorner` is the subtype of `Word a b × ℕ` with the two strict bounds and unequal neighboring Option-valued letters. The bounds ensure both accesses are `some`, including for empty words. |
| τ swaps the two adjacent letters and leaves k fixed | Existential τ has `(τ p).val.2 = p.val.2`; its word is exactly the two `.set` operations interchanging positions k-1 and k. `.getD false` reads actual in-range letters here, so the default is never used. τ's codomain asserts preservation of word counts and mixed-corner membership. |
| Fixed-point-free involution | `Function.Involutive τ` and `∀ p, τ p ≠ p`. |
| Coordinates agree at every other vertex | For every ℓ≤a+b with ℓ≠k, both prefix count equalities are asserted. |
| Inversion counts differ by 1 | The explicit disjunction `I(τp)=I(p)+1 ∨ I(p)=I(τp)+1`. |
| Deleted evaluated sequences agree | Universally in X,Y,x,y,p, `(evaluate (τ p).val.1 x y).eraseIdx k = (evaluate p.val.1 x y).eraseIdx k`. Repeated entries remain allowed. |
| Opposite signed coefficients | `sign (τ p).val.1 * (-1 : ℤ)^k = -(sign p.val.1 * (-1 : ℤ)^k)`. |
| Finite labeled sum is zero | Existential `hM : (Set.univ : Set (MixedCorner a b)).Finite` supplies all labeled corners as `hM.toFinset`; the stated sum of integral scalar multiples of basis symbols is zero, universally for the input strings. Finiteness is a conclusion, never an extra assumption. |
| Empty M if a=0 or b=0 | `IsEmpty (MixedCorner 0 b) ∧ IsEmpty (MixedCorner a 0)`, including a=b=0. |

Dependency declarations read and used:

- `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`, `Free.exists_set`, and
  `free_iff_set` (lines 42–50): the recorded free-module notion is existence of a basis.
  The standard finitely-supported-functions module realizes the free module on strings;
  there is no replacement free-module predicate or arbitrary supplied group.
- `Sheaf.AlgebraicTopology.ShuffleHorizontalFaceReindexing`,
  `AlgebraicTopology.ShuffleHorizontalFace.Word`, `horizontalCount`, `verticalCount`,
  `inversions`, `sign`, `evaluate`. I read all signatures and their construction docstrings,
  including the bounds used in evaluation. These exact definitions are reused without a copy.
  Its main horizontal-face theorem is not assumed in this theorem's statement.
- `Mathlib.GroupTheory.Perm.Fin`, `Equiv.Perm.sign_eq_prod_prod_Ioi`, lines 508–511:
  the permutation sign is the product of the comparison factors; this is the exact
  recorded Mathlib match of `lem-sfb-permutation-sign-inversion-product`.
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`, `Finset.sum_involution`, generated
  by `to_additive` from `prod_involution` at lines 663–682: the finite cancellation tool
  named by `lem-sfb-finite-involution-sum-zero`. This module is a plain proof import.
- `Mathlib.Data.Set.Finite.Basic`, finite-set conversion used to state the full sum
  without assuming a chosen Fintype on the list subtype.

Searches actually run for this assignment:

- msearch LeanFinder: “Swapping neighboring horizontal and vertical steps in a shuffle path
  reverses the inversion sign and cancels the deleted intermediate vertex boundary sum”.
  Eight hits, on `ComplexShape.σ_ε₂`, `ComplexShape.σ_ε₁`, their total-complex symmetry
  variants and a loop homotopy; none states the binary-word cancellation theorem.
- msearch Loogle: `"sign", "inversions"`: zero hits.
- msearch grep: `shuffle|mixed.corner|lattice.path`, subdirectory `AlgebraicTopology`:
  zero hits.
- msearch LeanSearch: “A finite sum of signed shuffle paths cancels after deleting
  intermediate vertices at mixed adjacent horizontal vertical steps”: eight hits,
  including `Finset.sum_cancels_of_partition_cancels`, `Fin.add_sum_removeNth`, graph
  walks and free-group cancellation; no exact match.
- `rg -n -i 'shuffle|mixed.corner|lattice.path'` in the upstream project, Sheaf and
  `dag/lean_names_upstream.json` found the landed horizontal-face helpers and the
  downstream lattice-path boundary theorem, neither an exact statement of this node.
  The downstream theorem is deliberately not imported: its proof uses this item.
- `rg -n 'mixedCorner|MixedCorner|mixed_corner_cancellation'` over Mathlib, upstream,
  Sheaf and the upstream name index found no existing declaration with these names.
- The item-id search in `lean/WeilConjectures` found no existing statement.
- Read the pinned Mathlib sources directly for permutation sign and finite involution
  summation. There is no reason to create another notion for either one.

Edge cases checked: n=0 gives the empty permutation, sign one and no corners; n=1
has no interior mark; a=0 or b=0 gives no mixed pair. For a=b=1 the two mixed words
swap and their inversion numbers are 0 and 1. Arbitrary repeated entries and constant
input strings are included: pairing is on (word,mark), not on distinct evaluated strings.
Empty X or Y are not excluded; they admit no nonempty input sequence, so universal
quantification over such inputs is correct. Universe u and v are independent.

An exhaustive auxiliary enumeration for a,b=0..4 checked 758 labeled mixed corners:
permutation inversions, preservation of the word counts and mark, no fixed points,
unchanged retained prefix counts, inversion difference one, and vanishing sums for
constant and alternating repeated-value input strings. All checks passed. This is a
statement sanity check, not a replacement for the postponed Lean proof.

The required `scompile.py` compiled the delivered module both in its sandbox and under
its library module name in 1.0 seconds each, with no errors or warnings. Every variable
and universe is explicitly bound. All source lines are at most 100 characters.

## Repair of return at 43c3a8516ff6

H2 / theorem-stmt_dep: replaced the sandbox-added theorem dependency
`lem-sfb-shuffle-horizontal-face-reindexing` by the new definition node
`def-sfb-shuffle-word-combinatorics`. The new record has `existing: true` and lists
exactly `Word`, `horizontalCount`, `verticalCount`, `inversions`, `sign`, `evaluate`
in `AlgebraicTopology.ShuffleHorizontalFace`. The theorem node is absent from both
statement and proof dependencies. The delivered Lean module is byte-identical to
the returned packet (SHA256
`75486a90c89aa22b0de5c82379c17e1b60213cb72a06a3a337058023aec611dc`).

The initial required dry run of the saved packet passed as acc57a6e36c. Comparison
with the current main node found only the saved `lean` record and additional
`stmt_deps`; all accepted statement and proof fields are retained. This ownership
repair changes no mathematical statement, definition data or theorem signature.

## New nodes

`def-sfb-shuffle-word-combinatorics` owns the six existing plain definitions in
`Sheaf.AlgebraicTopology.ShuffleHorizontalFaceReindexing`, lines 33–83, with no
new module. Its statement is exactly the opening combinatorics of the item and
the horizontal-face node, agent-written input to paragraph (3) of the latest
blueprint's direct-images proof. It introduces arbitrary natural a,b and words
with the stated length and letter counts (`Word`); the two prefix counts are
`horizontalCount`, `verticalCount`; the VH-pair cardinality is `inversions`;
`(-1)^I` is `sign`; and the n+1 evaluated vertices are `evaluate` with arbitrary
independent-universe input types and no restriction on repeated entries.
The extra length predicate in `Word` merely records n=a+b; its value is forced by
the two Boolean letter counts. At a=b=0 the evaluation is the single vertex;
at either zero axis the same prefix-count construction applies. Evaluation's
indices are bounded by the full counts using `List.take_sublist` and `count_le`.
No data depend on the postponed horizontal-face theorem.

Searches run for this repair: `blueprint_refs.py search shuffle` returned zero
blueprint nodes; `ancestor` returned None. DAG rg for the proposed id and the
recorded word declaration found only the horizontal-face theorem node, no
separate definition owner. msearch LeanSearch on binary shuffle words, prefix
counts, inversion, sign and evaluation returned Dyck words and permutation sign
lemmas, which do not define this notion. msearch LeanFinder on Boolean shuffle
words with fixed counts returned Coxeter alternating words, Dyck words and
permutation sign, also different notions. msearch grep for
`ShuffleHorizontalFace|horizontalCount|verticalCount|shuffle.*word` returned zero
Mathlib hits. Direct rg over upstream, Sheaf and the upstream-name index found
only the existing horizontal-face module; its full definitions and docstrings
were read. Thus this is an existing-declaration attachment, never a second
construction. The exact msearch query/result records are in the new node.

## Repair self-check by Q73

Read the new definition node against all six source definitions and rechecked
its use in the item: every shared combinatorial notion is supplied, with the
same universes and edge cases. The main module is unchanged; the maintainer's
independent reading already accepted all its mathematical clauses. The theorem
node's statement is not an input to any definition, nor to the mixed-corner
statement. Its absence from proof_deps is correct because no proof step invokes
the horizontal-face reindexing theorem. No other point was returned.

## Resumed validation

The resumed saved-packet dry run found the new definition node missing the
required `import_flags` key. Added `import_flags: []` as requested by preflight.
The Lean source remains byte-identical, and the existing six definition signatures
were reread directly from the live read clone. The only differences from the
current item node remain its `lean` record and the added definition dependency.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
