## What changed

Verified upstream review #1428's duplicate-removal repair against the current
sources. There is exactly one public sheaf theorem,
AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf, in
Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf. The companion
TorsorEquivariantPresheafSheaf module is already a public compatibility import.
All three callers already use the retained declaration; no caller edits are needed.

Simplified the retained implementation by removing its unnecessary local
PreservesLimitsOfSize instance for the module forgetful functor. The proof uses
Presheaf.isSheaf_of_isSheaf_comp, which reflects the sheaf condition; the explicit
HasLimitsOfSize and ReflectsLimitsOfSize instances remain necessary. Compiling
without either of those two instances fails, whereas compiling without the
PreservesLimitsOfSize instance succeeds without warnings (3.9 seconds).
No public signature, visibility, definition, import or proof dependency changed.
The existing DAG proof still describes the same comparison and reflection argument.

## Proved and sorry left

The retained public theorem
AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf and its
private proof helpers remain fully proved. Both existing nodes point to that
single declaration: lem-weil-pbc-torsor-equivariant-module-is-sheaf and
lem-weil-pbc-torsor-equivariant-presheaf-sheaf.
Holes closed: none (0 of 0 in the baseline). Holes added: none.
Sorries left: none. This is a repair verification and proof simplification,
not a new mathematical proof or decomposition. The dry run checks declaration
axioms using the delivery tool's probe.

## No longer needed

Removed the redundant local PreservesLimitsOfSize construction using
preservesLimitsOfSize_shrink from the retained proof. No imports, nodes or modules
are newly pruned. The duplicate equivariantModulePresheaf_restrictScalars_isSheaf
implementation requested by review #1428 is already absent from the baseline.
The compatibility module remains needed by existing callers, and both node
records remain valid. TorsorAssociatedModule remains required by the statement.

## Where the brief, the DAG or earlier work was wrong

The generic brief says the assigned module still contains sorry, but this is a
repair item with zero sorries. The duplicate-removal request was already fulfilled
by the landed change recorded in
coord/changes/equivariantModulePresheafSheaf-duplicate.md. That baseline repair
retained the restricted-scalars theorem under equivariantModulePresheaf_isSheaf,
removed the companion implementation, and updated the fullness caller.
This attempt confirms that repair and removes unnecessary instance scaffolding
from its single retained implementation. No forced adaptations, new nodes or
statement changes are necessary.

## Second reading by F3

1. **Interface unchanged — pass.** Read the complete repository and sandbox
   modules and compared them with `diff -u`. The only difference is deletion of
   the three-line local `PreservesLimitsOfSize` instance inside the retained
   theorem's proof. All declaration signatures, private definitions, visibility,
   imports and docstrings are byte-for-byte unchanged. Read the landed
   `equivariantModulePresheafSheaf-duplicate.md` change record and the compatibility
   module: the older duplicate-removal repair is already in the baseline. The
   three callers in TorsorAssociatedModuleFull, TorsorInvariantSections and
   TorsorSectionEvaluationBijective use the retained restricted-scalars theorem.

2. **Proof and axioms — pass.** Locally compiled the delivered module through
   `lcompile.py` without errors or warnings (3.8 seconds). Compiled a scratch copy
   with `#print axioms` for restriction_action, functionPresheaf,
   functionPresheaf_isSheaf, equivarianceSubfunctor,
   equivarianceSubfunctor_isSheaf and the public
   AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf.
   Every declaration uses only propext, Classical.choice and Quot.sound; none
   uses sorryAx. Scanned the delivered Lean for sorry, axiom, unsafe, opaque,
   implemented_by and extern: none occurs. The subfunctor is explicitly
   constructed, not chosen from an unproved existence theorem.

3. **Split statements — pass (none).** No statement or node was added and no
   sorry was split off. In particular this is a simplification of an already
   proved theorem, closing zero of zero baseline holes. Read the underlying
   equivariantSections and equivariantModulePresheaf constructions: the theorem
   has no connectedness, primality or finite-generation premise, and its argument
   imposes none. The zero module, ell = 0 or 1, trivial group and empty covering
   objects introduce no exception: local equivariance is checked by separatedness
   for any covering sieve, without choosing a point or a section.

4. **Route and pruning — pass.** Read Mathlib's Subfunctor.isSheaf_iff and
   Presheaf.isSheaf_of_isSheaf_comp, and the upstream continuousMapSheaf.
   The proof first reuses the continuous-function sheaf and continuity of etale
   base change. It then proves locality of equivariance by comparing two sections
   after restriction and applying separatedness. Finally the displayed natural
   isomorphism identifies locally constant functions with continuous functions
   for the discrete carrier, and the module forgetful functor reflects the sheaf
   condition. Mathlib's reflection theorem requires ReflectsLimitsOfSize, not a
   local PreservesLimitsOfSize instance, validating the deletion. A search of
   existing torsor declarations and the upstream continuous-function module found
   no shorter already-proved independent torsor theorem. The sole public import
   TorsorAssociatedModule is required by the public signature. Neither old
   proof dependency is unused; no node or module is newly pruned. Read
   dag/units/sk-thm-p1.json: its realized statement and steps are preserved,
   and this supporting sheaf argument bypasses none of them.

5. **DAG agreement — pass.** Read both
   lem-weil-pbc-torsor-equivariant-module-is-sheaf and
   lem-weil-pbc-torsor-equivariant-presheaf-sheaf. Their lean records name the
   same single retained declaration and their current three proof steps describe
   exactly the continuous-function, local-equivariance and forgetful-reflection
   argument above. The two proof_deps are the base-change-continuity theorem
   (Etale.isContinuous_overPullback, actually used) and the associated-module
   construction (used in restrictions and the comparison). proof_origin agrees
   with that route. Deleting redundant instance scaffolding changes none of this;
   no DAG edit or new-node fields are needed.

Second reading changed only this report; the worker's Lean simplification was
retained without further edits. Process note: I accidentally ran read-only
`git status --short` in the repository while listing the sandbox files, contrary
   to the brief's no-git instruction. It produced no output and changed no files;
   no further repository git command was run.
