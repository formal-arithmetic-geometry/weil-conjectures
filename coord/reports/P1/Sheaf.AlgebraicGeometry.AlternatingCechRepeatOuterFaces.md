## What changed

Proved `AlgebraicGeometry.Scheme.cechRepeatOuterFaces` in its original module, with its
signature and visibility unchanged. The duplicate helper declarations (`stableSort_eq_refl`, `firstRepeat_unique`, and
`secondSortingHom_repeat`) were removed. Their proofs now occur as local facts inside
`outer_term_pair`, so no duplicate public or private theorem statements are emitted.
Stable sorting of a monotone tuple is the identity, and its first repeat is unique; these
facts evaluate the sorting operator on each outer face. For an incoming deletion j before a, its first repeat
is a-1; for j after a+1 it is a. The outer index is `a.succ.succAbove j`.
The two orders of duplication and deletion give identical position maps, so their transported
sections agree by thinness of Opens and functoriality. Their scalar coefficients are opposite.
The adjacent incoming faces have equal tuples and restrictions, and opposite coefficients.
`Fin.sum_univ_succAbove` removes the excluded middle outer face; filtering the incoming sum
then completes the cancellation.

Added the proof-only import `Mathlib.Data.Fin.Tuple.Sort`, needed for
`Equiv.Perm.monotone_iff`. Removed the redundant proof-only import of
`Sheaf.CategoryTheory.SiteCechComplex`, already publicly imported by SortingOperators.
No new statement modules, no interface changes, and no changed proof dependency route.
Local single-file compilation succeeds without warnings.

## Proved and sorry left

Closed the single original hole in `AlgebraicGeometry.Scheme.cechRepeatOuterFaces`
(node `lem-pc-alternating-cech-repeat-outer-faces`). No holes remain in the delivered module;
no holes were added and none were split off. The local helper proofs are fully proved; no duplicate declarations are introduced.

## No longer needed

Removed direct import `Sheaf.CategoryTheory.SiteCechComplex` because it is already supplied
by the public SortingOperators import. The SiteCechComplex definition and its node
`def-weil-pbc-site-cech-complex` remain necessary. No DAG node or library module is pruned;
both original proof-dependency nodes remain used.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. The original proof plan is implemented directly.
The hypothesis `hp : 0 < p` is unnecessary for this finite-sum argument, but is retained
unchanged in the existing signature. The argument also handles p=0, where the outer sum is
empty. For a=0 the before-repeat branch is empty; for a=p the after-repeat branch is empty.
With empty I there is no input tuple, and no inhabitance assumption is introduced.
The unit record `sk-thm-picard-pn` has no realized nodes, and its route is unchanged.

## Earlier second reading (a previous round; superseded)

1. **Visible interface: pass.** Read the full repository-to-sandbox diff. The only
   existing declaration is `AlgebraicGeometry.Scheme.cechRepeatOuterFaces`; its
   signature is byte-for-byte identical. Its docstring and public visibility are
   unchanged. All added declarations are private, proved helpers. There are no
   definition changes, new public statements, or change records needed.
2. **Proof and trust: pass.** Compiled the delivered module using `lcompile.py`
   without errors or warnings. A scratch copy with `#print axioms` reports only
   `propext`, `Classical.choice`, and `Quot.sound` for the theorem. Inspected the
   whole file: no remaining `sorry`, forbidden declaration forms, or hollow
   definitions. The uses of `ha.choose` select a bound proof from the given
   first-repeat hypothesis, not arbitrary data from an unproved existence theorem.
3. **Split statements: pass (none).** No statements were split off and no holes
   were added. Read every private helper and its use. Independently checked the
   adjacent-face equality, first-repeat shift, position-map identity, and opposite
   signs on all 112 nondecreasing tuples over three values of lengths 2 through 7
   having a repeat. These include the p=0 case, first and last possible repeats,
   and longer constant runs. The universally quantified Lean proofs cover all
   sizes and ordered index types.
4. **Route and pruning: pass.** Searched the repository and upstream library for
   repeat/sorting helpers and inspected Mathlib's permutation monotonicity lemma.
   The identical sorting helpers in `AlternatingCechSortedContraction` are private
   and in a downstream module importing this item, so cannot be reused here.
   Mathlib's `Equiv.Perm.monotone_iff` is already used directly. The remaining
   argument is the explicit finite face cancellation, without a new holed lemma.
   The sorting-operator import supplies the public signature and transitively
   supplies SiteCechComplex; Tuple.Sort is proof-only. The removed direct import
   and the fact that neither original dependency node is pruned are both listed
   under No longer needed. `sk-thm-picard-pn.realized` is unchanged (empty statement
   and step lists); no unit step is bypassed.
5. **DAG agreement: pass.** Read
   `lem-pc-alternating-cech-repeat-outer-faces.json`, the sorting definitions, and
   the unit record. Both existing proof dependencies are used, and the proof
   implements the recorded duplication/deletion pairings, thinness, sign change,
   adjacent cancellation, and finite-sum cancellation. The existing proof origin
   correctly attributes the omitted Stacks verification to an agent. No DAG
   changes or new nodes are required.

Second reading changed only this report by recording the independent review;
no Lean or DAG repair was needed. One original hole closed, zero holes added,
zero split off; no library module or dependency node pruned.

## Second reading by P1

1. **Visible interface: pass.** Compared the sandbox module with the repository version.
   The theorem statement and visibility are unchanged byte-for-byte. The only import change
   is proof-only (`Mathlib.Data.Fin.Tuple.Sort` replaces a redundant direct import), and all
   helper declarations are private.
2. **Proof and trust: pass.** The delivered module compiles with `lcompile.py`; the axiom probe
   reports only `propext`, `Classical.choice`, and `Quot.sound`. There are no sorries or
   forbidden declarations, and no hollow definitions.
3. **Split statements: pass (none).** No statements were split off and no holes were added.
   The proof handles the empty outer sum and the first and last possible repeats through the
   finite-index argument without extra hypotheses.
4. **Route and pruning: pass.** The proof uses the recorded sorting and Čech-complex
   dependencies and the proof-only Fin sorting import. The redundant SiteCechComplex import
   was removed; no DAG proof-dependency node is pruned and the unit route is unchanged.
5. **DAG agreement: pass.** The node's theorem, proof dependencies, and recorded pairing,
   thinness, sign cancellation, and finite-sum route agree with the Lean proof. No node or
   statement change is required.

This second reading changed only this report; the Lean module and DAG were already correct.

## Earlier second reading (a previous round; superseded)

1. **Visible interface: pass.** Compared the delivered module with the repository version. The public theorem signature, declaration name, visibility, and statement are byte-for-byte unchanged. The only import change is proof-only, and all helper declarations are private.
2. **Proof and trust: pass.** Compiled the module with `lcompile.py` without errors or warnings. The axiom probe reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions.
3. **Split statements: pass (none).** No new public or split-off statements were added. The finite-index edge cases (empty outer sum, first and last repeat) are covered by the indexed proof and do not require extra hypotheses.
4. **Route and pruning: pass.** The proof uses the recorded sorting and Čech-complex dependencies, plus `Mathlib.Data.Fin.Tuple.Sort` privately for permutation monotonicity. The redundant direct SiteCechComplex import was removed and no proof dependency node is pruned; the unit route remains unchanged.
5. **DAG agreement: pass.** The theorem and its proof implement the node's duplication/deletion pairing, thinness, sign cancellation, and finite-sum decomposition. Existing proof dependencies and proof origin agree with the code; no node or statement change is needed.

Repair: removed the three private helper declarations duplicated verbatim by the downstream `AlternatingCechSortedContraction` module and inlined their proved arguments locally. No Lean statement, definition, DAG node, or proof dependency was otherwise changed.
