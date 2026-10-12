## What changed

Reduced `AlgebraicGeometry.Scheme.cechFirstSortingBoundary` without changing its
signature or existing docstring. Its Lean proof expands the outgoing differential,
distributes restrictions and integer multiples over finite sums, and partitions each
term according to whether the deleted original label equals the junction label.
It then combines two strictly partial identities using associativity of addition.
Two proof-only imports provide those identities. The original sorting-operator
public import remains. Updated the item's proof, proof_deps and proof_origin.

All three modules compile cleanly with lcompile.py --all. Independently checked the
two combinatorial coefficient identities on 1,961 tuples of lengths 2 through 6:
all tuples over three values and all permutations of distinct entries. This includes
p=0, repeated values and constant tuples. This finite check is supporting evidence,
not a proof of either remaining theorem. The empty index type has no tuple t.
Read Stacks Tag 01FM, equation cohomology-equation-first-homotopy; its verification
is explicitly omitted. The new docstrings spell out the labelled-deletion argument,
including separate prefix/tail sign exponents and product-map compatibility.
The unit sk-thm-picard-pn and its route are unchanged.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.cechFirstSortingBoundary`
(node lem-pc-alternating-cech-first-sorting-boundary), by decomposition.
No sorry remains in the item's module.

Added two holes, each the whole proof of a public named theorem in its own module:

- `AlgebraicGeometry.Scheme.cechFirstSortingJunctionDeletions`
  (lem-pc-alternating-cech-first-sorting-junction-deletions): only the outgoing
  deletions of the repeated junction label give successive partial stages.
- `AlgebraicGeometry.Scheme.cechFirstSortingNonjunctionCancellation`
  (lem-pc-alternating-cech-first-sorting-nonjunction-cancellation): only the outgoing
  deletions of other labels cancel the incoming expansion.

This is one upper hole reduced to two lower holes, not a sorry-free proof of the
mathematical result. The partition and the combination are complete Lean proofs.
Neither remaining statement includes the whole upper boundary formula.
No data is chosen from an unproved theorem and no definition is added.

## No longer needed

None. No original imports, nodes or modules are removed. Both original definition
nodes are still used; the two new statement modules are needed by the proof.

## Where the brief, the DAG or earlier work was wrong

The existing single proof step includes both substantial cancellation computations
but its two dependencies only define the objects. They do not state either
computation. No suitable exact statement was found in either library root or
Mathlib. LeanFinder returned Dold-Kan and simplex-category results, not this
explicit filtered permutation calculation. Loogle found Finset.sum_filter, useful
for partitions but not the cancellation. LeanSearch returned Internal Server Error;
recorded as unavailable. Grep found finite-sum infrastructure only. Blueprint search
for sorting returned no imported blueprint node.

## New nodes

`lem-pc-alternating-cech-first-sorting-junction-deletions` is realized by
Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingJunctionDeletions. It retains only
the two deletions of the repeated original label and identifies their contribution.
Its source is the junction part of the omitted verification of Stacks 01FM.

`lem-pc-alternating-cech-first-sorting-nonjunction-cancellation` is realized by
Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingNonjunctionCancellation. It
retains all other outgoing deletions and the incoming differential. Its source is
the nonjunction part of the same verification. The prefix and tail cases have
opposite incoming/outgoing coefficients, as detailed in its docstring.

No interface changes and no change records or forced adaptations.

## Second reading by H3

1. Compared all delivered modules with the repository. Only the original boundary
   theorem existed there: its signature and original docstring are byte for byte
   unchanged. Its two new imports are proof-only imports. There are no definition
   changes, interface adaptations or change records. Verdict: pass.
2. All three modules compiled cleanly through lcompile.py --all. An independent
   scratch copy with #print axioms for all three theorems reports only propext,
   Classical.choice, Quot.sound and sorryAx. The latter remains because the two
   new public theorems have their whole proofs left sorry; the original module
   has no direct sorry. No forbidden declarations, hollow definitions or chosen
   witnesses were introduced. Verdict: valid conditional proof, not a completed
   axiom-free result.
3. Read both new statements and their labelled-deletion proofs. The junction lemma
   treats only the two occurrences of the junction label, and the nonjunction
   lemma only the remaining outgoing terms paired with incoming faces. Each is
   strictly part of the original computation, not a renamed boundary identity.
   Rechecked signs by moving a label to the junction or deleting it, and checked
   transport equality using indexMap_pr and SiteCechComplex.universal. Stable
   sorting survives deletion because increasing renumbering preserves original
   label order, including ties. Independently reran both identities on 1,961
   tuples of lengths 2 through 6, keeping original labels in the coefficient keys
   instead of merging equal tuple values; the smallest degree, constant tuples,
   repeated values, and all distinct permutations passed. Empty I has no t.
   New LeanFinder and Loogle queries for permutation deletion signs, and rg for
   deletion, sorting and homotopy infrastructure found sign_cycleIcc_of_le and
   erasure ingredients, but no theorem closing either full partial identity.
   Neither hole can be closed in a few minutes from these ingredients. Verdict:
   true, needed partial statements, with source and complete informal proofs.
4. Read the partition proof top downward: it unfolds the actual outgoing operator,
   distributes the sums, partitions by the deleted original label, then combines
   J with N+incoming=0 by associativity. No shorter existing route was found.
   Each import is needed; the public sorting-operator import supplies signature
   definitions, and both new imports supply only proof lemmas. Both old dependency
   nodes remain used, so No longer needed is complete. The unit sk-thm-picard-pn
   has no sorting-specific realized entries, and its statement, steps and existing
   realized record are untouched. Verdict: pass, no pruning or route bypass.
5. Compared old/new boundary node fields: only proof, proof_deps and proof_origin
   change. Their steps and dependency union match the Lean proof. Both new nodes
   have the requested source, statement dependencies, search records, provenance,
   blueprint chain, chapter, unit, created and lean records. Their Lean signatures
   now preserve the source whitespace verbatim. Verdict: pass.

Second-reading changes: expanded the two new proof docstrings and matching node
proofs to justify uniqueness of both permutation filters, clarified that the tail
position b is a position in τ (junction position b+1), synchronized the new node
Lean statements verbatim, and recorded independent searches and this review.
The original proof was right and is unchanged. Closed one original named hole by
adding two strictly smaller named holes: this delivery is a decomposition, with
net holes closed minus added = -1; no theorem becomes independent of sorryAx.
