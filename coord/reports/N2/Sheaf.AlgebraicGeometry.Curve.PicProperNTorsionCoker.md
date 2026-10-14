## What changed

Reworked `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker` to use
`AlgebraicGeometry.Scheme.exists_mulEquiv_prod_ker_picDegreeHom` from
`WeilConjectures.AlgebraicGeometry.Curve.Picard` directly. The proof installs the original
structure morphism, derives irreducibility and smooth relative dimension one, identifies
the degree kernel with `f.picZero`, and retains the explicit integer-cast kernel calculation
and the first isomorphism theorem. Its signature and all public imports are unchanged.
Updated the existing node's proof route and added module documentation.

This item is a listed duplicate repair, not a fresh sorry-proof item. The cited replacement
is absent from the supplied source and compiled library, so the available source-library
splitting is used instead. No existing caller needs adaptation.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
(node `lem-sc-pic-proper-ntorsion-coker`) has a complete local proof, conditional on the existing divisibility dependency.
The baseline module already
had zero local sorries. Holes closed: none. Holes added: none. Sorries left in delivered
modules: none. This is a proof-dependency pruning repair, not new net hole progress.

The conclusion and hypotheses are identical to the baseline. In particular the n = 1 case
is retained, n = 0 is excluded by `(n : k) ≠ 0`, and the proof of the kernel equality
constructs an nth root in both factors rather than assuming the desired cokernel result.

## No longer needed

Removed the proof imports:

- `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition`;
- `Mathlib.Algebra.Group.TypeTags.Hom` (the needed API is already available).

The Sheaf declaration `Scheme.Hom.exists_mulEquiv_prod_picZero`, including its unused
compatibility with the inclusion of Pic0, is no longer used by this module. The mathematical
node `lem-sc-pic-proper-decomposition` remains needed and is realized directly by the
source-library splitting. `lem-sc-pic-proper-ntorsion-div` remains needed. No other node is
claimed globally unreachable; other importers may still need the removed Sheaf module.
The unit's route and its statement are unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic brief says this module still contains sorry, but its checked-in theorem is
already fully proved. `coord/repairs.txt` identifies the actual reason for dispatch:
the upstream duplicate review (#1428) cites
`AlgebraicGeometry.Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient` in
`WeilConjectures.AlgebraicGeometry.Curve.Jacobian` as a replacement.

Neither the module nor that declaration exists in this project's `lean/WeilConjectures`,
the supplied source checkout, or the current local source mirror. A compiler check importing
both `WeilConjectures.AlgebraicGeometry.Curve.Picard` and
`WeilConjectures.AlgebraicGeometry.Picard.Jacobian` reports:
`Unknown constant AlgebraicGeometry.Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`.
The same compiler check confirms the available declaration
`Scheme.exists_mulEquiv_prod_ker_picDegreeHom`. Consequently deleting the public cokernel
theorem and repointing callers to the review's named replacement would break the supplied
library. This delivery keeps the public statement and removes the redundant Sheaf splitting
wrapper from its proof instead. The duplicate review requires reconciliation with the
actual upstream revision before its proposed declaration replacement can be performed.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface — pass.** Diffed the sole delivered Lean module against the
   repository copy and compared the theorem signature byte for byte: identical. There
   are no definitions, new declarations, interface changes, or forced adaptations. All
   six public imports are unchanged; the two proof imports are plain imports.
2. **Proof and axioms — pass with existing dependency holes.** Compiled the module with
   `lcompile.py`: exit 0, no warnings or errors. Scanned for sorry, axiom, unsafe, opaque,
   implemented_by, extern and skipKernelTC: none. Compiled a scratch copy with
   `#print axioms`: the cokernel theorem uses propext, Classical.choice, Quot.sound and
   sorryAx; the existing divisibility theorem also uses sorryAx, whereas the source
   splitting uses only the three permitted axioms. Thus this is a complete local proof,
   not an axiom-free completion of the target's dependency closure. The chosen splitting
   and roots are used inside a propositional proof, not as data of a new definition.
3. **Split statements — pass, none added.** No split-off theorem or new node is delivered.
   Checked the kernel calculation in both directions: it constructs the integer root
   using divisibility in Z and the degree-zero root using the existing divisibility
   theorem. For n = 1 the quotient and ZMod 1 are trivial; n = 0 is excluded by the
   unchanged field-cast hypothesis. No weakened replacement or restatement is involved.
4. **Route and pruning — pass.** Read the source splitting, the Sheaf wrapper and the
   divisibility theorem; searched the local library for the proposed duplicate and
   Mathlib for power-range/product quotient APIs. The proposed replacement remains
   absent. The direct source splitting removes a stronger wrapper while retaining the
   same degree splitting, Jacobian divisibility and first-isomorphism argument. The
   product quotient API does not supply a shorter geometric argument. Checked
   `dag/units/sk-thm-curveestimate.json` and the decomposition node's recorded source
   proof: the unit realization and degree-one splitting route remain unchanged. The
   blueprint markdown files are not installed on this machine; their recorded texts
   and the actual Lean source were read. No old proof_deps node is omitted: both old
   dependencies remain, with the explicitly used setup nodes added. The two removed
   imports are listed above; global unreachability is not claimed.
5. **DAG agreement — pass.** Compared the node JSON structurally: only proof,
   proof_deps and proof_origin differ. The dependency list is exactly the union of the
   proof-step uses; the statement, Lean declaration record, chapter and unit are
   unchanged. The proof text names the actual source-library declarations used.

Second reading changed only this report: clarified that the locally complete theorem
still inherits sorryAx from the existing divisibility dependency, and recorded the five
review checks. The Lean proof and node needed no repair. Holes closed: none; holes added:
none; no new split statements.

## Second reading by N2

1. **Interface — pass.** Independently diffed the sole delivered module against the
   repository. The existing theorem signature is byte-for-byte identical, all six public
   imports are unchanged, and no definitions or new declarations are delivered. The two
   proof imports are plain imports. No target, statement or definition changes.
2. **Proof — pass with existing dependency holes.** Independently compiled the scratch
   copy of the actual proof with `lcompile.py` and printed axioms for the cokernel theorem,
   the source splitting and the existing divisibility theorem. Compilation succeeded.
   The cokernel and divisibility theorem depend on propext, Classical.choice, Quot.sound
   and sorryAx; the splitting uses only the three permitted axioms. The delivered source
   contains no sorry or forbidden declarations, and no lines exceed 100 columns. All
   witnesses are local to a propositional proof; no arbitrary data definition is added.
3. **Split statements — pass, none.** No new statement, node or sorry is introduced.
   Read both directions of the kernel argument: nth powers vanish modulo n, and the
   converse obtains an integer root by divisibility and a degree-zero root using the
   existing divisibility theorem. For n = 1 both quotient and ZMod 1 are trivial; n = 0
   is excluded by the field-cast hypothesis. No restatement is used to hide a hole.
4. **Route and pruning — pass.** Read the actual upstream degree splitting, the Sheaf
   splitting wrapper and the divisibility proof. Independently searched the repository
   and local library for the alleged upstream cokernel duplicate: it is absent. Searched
   Mathlib product power-range APIs and Loogle for the first isomorphism theorem; these
   supply algebraic tools, not a shorter geometric replacement. Both old proof dependency
   nodes remain recorded, with the setup dependencies made explicit. The stronger Sheaf
   wrapper is bypassed using the source splitting and the kernel/carrier identification;
   its extra inclusion compatibility is unused. Both removed proof imports are listed
   under No longer needed. The unit record sk-thm-curveestimate and its realized statement
   remain unchanged; no unit step is bypassed. Global unreachability is not claimed.
5. **Nodes — pass after metadata repair.** Compared the node structurally with the
   repository: the intended changes are proof, proof_deps and proof_origin, and proof_deps
   is exactly the union of the steps' uses. Statements, source, Lean attachment, chapter
   and unit are unchanged. The sandbox also contained a stale reviewed_proof value from
   a different landing, outside the worker-owned fields. Restored that value from the
   repository so the node now differs only in the three intended proof fields.

Second reading changed the node's stale review metadata and appended this independent
review. The Lean proof required no changes. Holes closed: none; holes added: none;
split off: none. This is a local proof-dependency pruning repair, with zero net hole
progress and the existing divisibility dependency still open in its import closure.
