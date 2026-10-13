## What changed

Proved the exactness half of `AlgebraicGeometry.schemeCanonicalTensorShift_properties`
for the specified canonical shifts, without equating the localization universe with
the sheaf universe. Two proved private helpers adapt the source library's
`commShiftTensorRight_eq` and `isTriangulated_tensorRight` arguments to the already
constructed independent-universe shift structure. The first identifies the shift
on a K-flat representative by uniqueness of localization; the second transports
exactness from that representative to every derived object.

Split the right-unitor half into its own module and imported it for the proof only.
The original theorem signature and public imports are unchanged. Updated the
parent DAG proof to reflect the actual reduction. No definitions or existing
interfaces changed. The new statement is only the right-unitor conjunct; it does
not assert tensor exactness.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.schemeCanonicalTensorShift_properties`
(node `lem-sc-scheme-canonical-tensor-shift-properties`). Its complete proof combines
proved tensor exactness with the right-unitor lemma. There are no sorries in the
item module, and both private helpers are proved:
`DerivedCategory.IndependentTensorShift.independent_tensorRight_eq` and
`DerivedCategory.IndependentTensorShift.independent_tensorRight_exact`.

Added one hole:
`AlgebraicGeometry.schemeCanonicalTensorShift_rightUnitor`
(node `lem-sc-scheme-canonical-tensor-shift-right-unitor`). Its whole proof is
`:= by sorry`. This is a decomposition with exactness proved, not a claim of a
fully sorry-free proof of the original theorem. Holes closed: 1; holes added: 1.
The remaining statement has the exact degree-one square and K-flat hypotheses of
the original second conjunct. It handles the zero complex and empty scheme by the
same unit and localization identities; no extra hypotheses were added.

## No longer needed

No original imports or planned nodes can be pruned: they all describe the tensor,
shift and K-flat structures appearing in the statement. A trial direct proof import
of `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift` was removed because
that module is already publicly available through the tensor-structure imports.
No library module is removed from the target closure by this delivery.

## Where the brief, the DAG or earlier work was wrong

The generic source library's global `commShift₂CurriedTensor` and corresponding
exactness instance identify the Grothendieck and localization universes. They
cannot be applied directly to the independent-universe canonical scheme shifts.
The underlying one-variable K-flat exactness theorem has independent universes,
and the localization-uniqueness proof adapts without changing any construction.

Initially the compiled snapshot lacked `SchemeCanonicalTensorShift` and
`DerivedTensorShiftIndependentUniverse`. Both became available during work.
Unchanged temporary sandbox copies used to inspect compilation were removed;
the delivery contains neither dependency copy nor dependency modifications.

## New nodes

`lem-sc-scheme-canonical-tensor-shift-right-unitor`, module
`Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftRightUnitor`, isolates only the
right-unit shift calculation. Its source and full representative-complex proof
are recorded in the Lean docstring and DAG node. The second reader corrected the
source of the unitor calculation to the upstream `BifunctorShift` and `ShiftUnitor`
modules; Stacks Tag 08EU is a projection formula, not that calculation. Exactness is proved separately
in the parent, so the new lemma is strictly a part of the original argument.
The conservative command-level interface check requires the record
`coord/changes/H3-canonical-tensor-private-proof-setup.md`. It documents only
namespace-local proof setup for private proved helpers; no consumer is adapted.

## Second reading by H3

1. Compared both delivered modules with the repository. The parent theorem's
   signature is byte-for-byte identical; there are no definition edits, removed
   declarations, or changed public imports. The added import is proof-only.
   The new public statement is exactly the second conjunct. PASS.
2. Compiled both modules separately in dependency order through `lcompile.py`:
   no errors or warnings (12.1 s and 51.3 s). Checked all declarations and forbidden
   constructs; the sole textual sorry is the reported public right-unitor theorem,
   with no holed definition. The two private helpers are genuine localization and
   triangulated-functor proofs. A scratch copy prints their axioms and both public
   theorem axioms: both private helpers use only `propext`, `Classical.choice`,
   `Quot.sound`; the two public theorems additionally use `sorryAx` for the
   recorded remaining square. Delivery also runs the complete axiom probe. PASS.
3. Read the split-off proof in words and its node; the square has the original
   hypotheses and conclusion, strictly one part of the parent conjunction.
   Checked zero complexes, the empty scheme, and complexes concentrated in an
   arbitrary degree: the second tensor degree is zero, giving no first-variable
   Koszul sign. Independently searched LeanFinder, Loogle and both library roots
   using unitor/translation and unit/shift terminology. The closest upstream
   `rightUnitor_commShift` only evaluates at the unit first factor and identifies
   the universes; it cannot be applied to this statement unchanged. Its complex
   calculation supplies the documented representative proof, but completing the
   generalized descent is beyond a few-minute repair. PASS.
4. Read the proof top down and compared its private helpers with upstream
   `commShiftTensorRight_eq` and `isTriangulated_tensorRight`: this is the same
   proof with independent universes, using the existing one-variable exactness
   theorem. All original imports support public statement notions; no old
   proof dependency has been dropped. The unit record's `realized` fields are
   unchanged (the item is below the unit level). The report correctly calls this
   a decomposition, closing one hole and adding one, with no net hole reduction
   or closure pruning. PASS.
5. Diffed the parent node and checked the new node against its Lean declaration:
   existing changes are confined to proof/proof_deps/proof_origin; the new node
   has the prescribed source, searches, provenance, chapter, unit and exact Lean
   statement. Both proof plans agree with the code and the remaining square. PASS.

Changed only the new theorem's source documentation and its node's source/search
records, and completed this review report. In particular, [Stacks Tag 08EU]
(https://stacks.math.columbia.edu/tag/08EU) proves the projection formula; the
unitor calculation is instead in the upstream `BifunctorShift` and `ShiftUnitor`
files. [Tag 06YH](https://stacks.math.columbia.edu/tag/06YH) records derived tensor
as an exact functor. The existing parent statement and proof remain unchanged.
