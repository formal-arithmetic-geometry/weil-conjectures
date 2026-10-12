## What changed

`Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingIdentity` now proves
`AlgebraicGeometry.Scheme.cechFirstSortingIdentity` from one strictly intermediate
boundary calculation. Its original signature, visibility, docstring, and public imports
are unchanged. Proof-only imports add `Mathlib.Data.Fin.Tuple.Sort` and
`Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingBoundary`.

Proved private helpers construct partial sorting stages as actual finite sums, characterize
their two endpoint filters, evaluate the endpoints, and telescope consecutive differences.
`Tuple.eq_sort_iff` supplies stable sorting uniqueness without a new assumption. Degree zero
is proved directly: the differential of the duplicated singleton has two identical
restriction maps with opposite signs. Positive degrees unpack Mathlib's homotopy component,
apply the boundary calculation, telescope, and rewrite both endpoints.

Both delivered modules compile together. The remaining boundary calculation was also
checked independently over scalar cochains on three indices: 7,371 basis-coefficient checks
for tuple lengths 2–4 passed, including repeated and reversed entries. This is a finite
sanity check, not a proof of the remaining lemma. Empty index types give no tuple to evaluate;
the original zero-degree case is fully proved. The source at
https://stacks.math.columbia.edu/tag/01FM was read to verify the partial permutations and signs.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.cechFirstSortingIdentity`
(node `lem-pc-alternating-cech-first-sorting-identity`). No `sorry` remains in the item.

Added exactly one hole: `AlgebraicGeometry.Scheme.cechFirstSortingBoundary`, in new module
`Sheaf.AlgebraicGeometry.AlternatingCechFirstSortingBoundary`, node
`lem-pc-alternating-cech-first-sorting-boundary`. It states the uncancelled partial-stage sum
in positive degrees; it does not assert the desired endpoints or telescope them. Its body
is exactly `by sorry`, with the source and complete labelled-deletion argument in its docstring.

This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
The endpoint calculations, homotopy-component assembly, degree-zero case, and telescoping
are proved with no new holes or data chosen from unproved existence statements.

## No longer needed

Removed the redundant proof import `Sheaf.CategoryTheory.SiteCechComplex`; it remains
available through the required sorting-operators public import. The second reading also
removed `Mathlib.Tactic.Abel`, using Mathlib telescoping instead. Both original public
imports are required by the statement. No existing dependency node or module is pruned. The first sorting route and the unit's Cech route are retained.
No repeated-tuple (second sorting) theory is imported by this proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or forced adaptation was found. The original proof plan bundled
nonjunction deletion cancellation, endpoint evaluation, and telescoping into a single step.
The delivery isolates only the first calculation, and formalizes the other parts.
Stacks 01FM itself omits the verification; the new docstring explicitly writes out its
labelled-deletion argument and the node marks that expansion as written by T1.
LeanSearch was unavailable (Internal Server Error); LeanFinder, Loogle, and source grep ran.

## New nodes

`lem-pc-alternating-cech-first-sorting-boundary` records the strictly intermediate
positive-degree differential expansion after nonjunction cancellation, with the signed
partial-stage sum still unevaluated. It inherits the item's chapter and unit. Its sole new
module contains one public theorem and no new definitions. The parent node now describes
the compiled proof and names this dependency. No change records are needed.

## Second reading by T1

1. Compared both delivered modules with the repository: the boundary module is new;
   the existing target signature, visibility, and docstring are byte-for-byte unchanged.
   No public definition or public import changed, and no change record is required.
2. Compiled both modules in import order through lcompile.py, without errors or warnings.
   Inspected every proof and the actual finite-sum helper definition. Exactly one named
   theorem, cechFirstSortingBoundary, retains sorry; there are no forbidden declarations
   or hollow definitions. Explicit axiom prints show only propext, Classical.choice, Quot.sound for the
   endpoint/telescoping helpers; the target and boundary also have the expected sorryAx.
3. Read the boundary statement, its docstring argument, its node, and Stacks 01FM.
   It isolates the positive-degree nonjunction cancellation calculation, retaining the
   partial-stage sum; it omits the proved endpoints, telescoping, and degree-zero case.
   It is a strictly intermediate step, not the original identity under another name.
   Independent coefficient checks passed on every tuple of lengths 1–4 over three values
   (697 coefficients), including singleton, repeated, and reversed cases. Empty index types
   have no tuples. Fresh LeanFinder search for prism/differential cancellation and source
   searches found no existing theorem for these explicit operators. The cancellation is
   not a few-minute proof: it needs deletion/reindexing and permutation-sign lemmas.
4. Read the proof downward and checked all imports and old proof dependencies. Found
   Mathlib Finset.sum_range_sub' via a fresh Loogle search; replaced the induction/abel
   helper proof by it after Fin.sum_univ_eq_sum_range, and removed the Abel import.
   Corrected the omitted removal of the redundant SiteCechComplex import in this report.
   No old dependency node is unused. The unit sk-thm-picard-pn realized fields are empty
   in the repository; its prescribed Cech computation route is retained without alteration.
5. Compared the node diff with the actual proof: proof_deps is the union of the listed
   uses, the parent proof records the endpoints, zero case, boundary reduction, and
   Mathlib telescoping, and proof_origin attributes the expansion correctly. The new
   node has its complete source, proof, search, provenance, chapter/unit and Lean fields.

Changes: shortened telescoping using Mathlib, removed Mathlib.Tactic.Abel, updated the
parent node's telescoping step, corrected the import-pruning report, and added this review.
Verdict: valid decomposition, one original hole closed and one strictly intermediate hole
added; net zero holes, no dependency module pruned. The original identity still depends on
sorryAx through the explicitly reported boundary theorem.
