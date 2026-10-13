## What changed

Proved `Module.finiteFreeMap_residue_localization_strong` in
`Sheaf.RingTheory.FiniteFreeMapResidueLocalizationStrong` without changing its statement,
visibility, or public imports. Added proof imports `Mathlib.LinearAlgebra.Matrix.Rank` and
`Mathlib.RingTheory.TensorProduct.Free`.

Two fully proved private helpers implement the matrix argument. `split_of_unit_minor`
constructs a retraction using the inverse selected minor and identifies the cokernel with
the functions on the complement of its selected rows. `exists_nonzero_minor` uses equality
of row and column rank to choose a basis of rows over a field. Base change commutes with
this minor's determinant; the residue-field vanishing criterion puts the determinant
outside the prime. The bijective clause uses equality of residue-field dimensions and
`LinearMap.comp_eq_id_comm` for a finite free module over a commutative ring.

Updated the existing node's proof and proof_origin to describe these constructions.
No new nodes, statements, definitions, or adapted modules.

## Proved and sorry left

Closed the one original hole:
`Module.finiteFreeMap_residue_localization_strong`
(node `lem-pc-finite-free-map-residue-localization-strong`). Both clauses are proved.
No holes remain in the item and no holes were added. Both private helpers are proved.

Single-file compilation succeeds without warnings. The delivery dry run checks axioms.
The construction includes rank zero: for m=0 the selected minor is the empty matrix and
the cokernel coordinates are all target coordinates. For m=n=0 the same empty matrix
identities apply. If m>n the injective-fibre assumption is impossible; the full-row-rank
basis argument handles this without a separate hypothesis. The generic unit-minor helper
also works over the zero ring, although the original prime excludes that case.

## No longer needed

No existing imports, DAG nodes, or project modules were pruned. The original node has
no proof dependencies. During development the redundant direct imports
`Mathlib.LinearAlgebra.Matrix.ToLinearEquiv`, `Mathlib.LinearAlgebra.Isomorphisms`, and
`Mathlib.LinearAlgebra.FiniteDimensional.Basic` were removed; they are already available
through `Mathlib.LinearAlgebra.Matrix.Rank`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The plan's elementary row and column operations
are implemented as the explicit projection y - u(v(y)) and a quotient equivalence.
The square case reuses that inverse and commutativity of one-sided inverse identities
instead of separately constructing a second adjugate inverse. This stays below the unit
level: the unit record has no realized statement or steps attached to this node.

Mathlib searches: LeanFinder returned local-ring splitting/free-cokernel results and
principal-localization spreading results, but no exact principal-localization theorem.
Loogle found the matrix unit-determinant and nonsingular-inverse APIs. Ripgrep searches
of Mathlib and both project roots found no existing theorem matching this statement.

## Second reading by C4

1. **Interface and accidental changes.** Compared the delivered Lean module with the repository
version. The public theorem signature and visibility are byte-for-byte unchanged. The only
module additions are private proof imports and private helper theorems. The DAG statement is
unchanged; the delivered node proof records the actual minor and quotient argument.

2. **Proof and trust.** Compiled the module with `lcompile.py`; it succeeds without warnings.
The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `sorryAx`.
The proof uses only the stated matrix, tensor-product, and localization APIs; its declarations
therefore have only the permitted standard axioms (confirmed by the delivery probe).

3. **Statements and dependencies.** There are no split-off statements or new nodes. The two
private helpers are strictly internal reductions: a unit minor gives a split map and a quotient
by a finite free coordinate module, while injectivity over the residue field supplies the minor.
The existing theorem is proved exactly as stated, including the zero-rank cases. No matching
Mathlib or upstream theorem was found in the recorded searches or repository search.

4. **Pruning and route.** The two added imports are used by the proof and are proof-only imports;
no public import is unnecessarily exposed. No old proof dependency or module is unused. The
unit record's `realized` fields are empty, so this proof does not bypass a realized unit step.

5. **DAG and report agreement.** The delivered node's proof, proof origin, and Lean declaration
agree with the implementation: row-basis selection, determinant base change, localization at a
unit determinant, quotient equivalence, and the square bijective case. No change record is
needed because no existing statement or definition changed.

I changed only this report by adding this review section; no Lean source, declaration, or DAG
statement was changed during second reading.

Additional verification: appended `#print axioms` for both private helpers and the public
theorem to a scratch copy and compiled it through `lcompile.py`. All three report exactly
`propext`, `Classical.choice`, and `Quot.sound`. Independently checked the source argument at
https://stacks.math.columbia.edu/tag/00O0 (the local literature file is absent on this machine).
The second-reader Loogle and LeanFinder searches for an injective matrix's nonzero row minor
found only square-matrix injectivity and submatrix-invertibility APIs, not a replacement theorem.
The dry run passed compilation and preflight; the node-only proof-plan update makes this delivery
CODEX rather than AUTO.
