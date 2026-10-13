## What changed
Replaced the first worker's near-restatement `exists_reduced_flat_affine_preparation_data`
and unproved generic-point lifting lemma with a reduction before flatness and an affine
restriction lemma, each in its own module. The original theorem's signature is unchanged. The proof constructs the reduced preparation, invokes the existing
`exists_nonempty_open_flat_finitePresentation_restrict`, restricts the preparation,
and proves generic-point lifting by reflection of specialization along embeddings.
The existing docstring describes principal-open lifting; the shorter implemented route
uses the affine-open basis and affineness of universal homeomorphisms to obtain affine
inverse images. This changes no unit-level step.

`AffineReductionPreparation.lean` constructs the source as the reduction of the actual
pullback; it uses the existing named reduction theorem. `AffinePreparationRestriction.lean`
constructs affine opens and restriction maps and identifies the second universal
homeomorphism by a pullback square. New helper imports in the original module and the
reduction-theorem import in the reduction helper are proof-only imports.

## Proved and sorry left
The original hole closed is `AlgebraicGeometry.exists_reduced_flat_affine_preparation`.
The new helper `AlgebraicGeometry.exists_affine_reduction_preparation` is proved.
The new helper `AlgebraicGeometry.exists_affine_preparation_restriction` is proved.
There are no `sorry`s in any of the three delivered modules and no holes added.
The original hole count is 1, with 1 closed and 0 new: net +1 in the import closure.
This is a proof from existing dependencies, not a decomposition adding new holes.
The printed axioms of all three declarations contain only propext, Classical.choice,
and Quot.sound; in particular the imported dependencies introduce no sorryAx.
The first worker's two proposed holes are removed, not delivered under new names.
No data definition, arbitrary choice of data from an unproved existence theorem,
axiom, or forbidden implementation declaration is added.

## No longer needed
Removed the original module's direct proof-only import
`Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism` and its direct dependency edge
`lem-weil-pbc-reduction-universal-homeomorphism`; both are now used through the proved
reduction helper. This module remains in the transitive closure and is not pruned.
Every other old dependency remains directly used. No modules are pruned.

## Where the brief, the DAG or earlier work was wrong
The first worker's report claimed two new nodes but supplied neither. Both new theorem
docstrings lacked complete natural-language proofs. Its data theorem retained nearly
all of the original conclusion, without making the generic-flat theorem explicit in the
Lean reduction. The replacement separates reduction from generic flatness and restriction.
The report originally called this a proof; a reduction with remaining new holes must
instead be counted as a decomposition. No original statement or definition needed changing.
The Stacks source is absent from this machine's literature tree; the second proof of
[Tag 0559](https://stacks.math.columbia.edu/tag/0559) was read online.

## New nodes
`lem-sbc-affine-reduction-preparation` states preparation before flatness and local finite
presentation. It is proved using the original reduction dependency and elementary
pullback and generic-point arguments. Its node records the actual construction, taking
the reduction of the pullback, rather than choosing an unspecified witness.

`lem-sbc-affine-preparation-restriction` states restriction of an already reduced affine
preparation over a specified open on which the map is already flat and locally finitely
presented. It assumes no finite type condition on f and no generic-point hypothesis;
its construction is independent of reduction and generic flatness. Both nodes have
verbatim Lean signatures, complete docstrings, and all required Mathlib search kinds.
LeanSearch returned Internal Server Error for both queries and is recorded as unavailable;
LeanFinder, Loogle and grep supplied the completed searches.
No change record is needed: all existing statements, definitions and visibility are preserved.

## Second reading by R2
1. **Interface:** compared the delivered original module with the repository version and
   its node signature. The existing signature and docstring are unchanged. The two helper
   modules add new statements; no existing statement, definition, or target changes.
2. **Proof:** compiled the revised three-module set using only `lcompile.py` during the
   review. No hollow definitions or forbidden declarations occur. Final clean compilation
   and explicit axiom results are recorded below.
3. **Split statements:** searched using LeanFinder, Loogle and grep, with LeanSearch recorded unavailable, and searched the local
   Sheaf and upstream library. The searches found component lemmas, not duplicate preparation
   theorems. Reviewed the constructions on the empty source, an identity map of an integral
   affine scheme, and a nonreduced irreducible affine base. The generic point excludes an
   empty base. Reduction and restriction are separate parts of the source argument; neither
   helper simply renames the original target.
4. **Route and pruning:** the original generic-flat theorem is explicitly invoked after
   reduction, and the original reduction theorem is used in the reduction helper. Thus both
   original dependency routes remain. The unit `sk-prop-normal-form` has empty `realized`
   arrays in the checked-out record; this lower-level change neither changes that record
   nor bypasses its units. All statement imports are public and all added proof imports
   are private imports. No transitive module is pruned.
5. **DAG:** replaced the original node's proof and proof dependencies with the written
   reduction/generic-flat/restriction route. Added nodes for both new helper statements;
   their Lean records match the signatures, and their proof descriptions follow the code.

Second reading replaced the two proposed splits with proved reduction and affine restriction,
proved generic-point lifting directly, made generic flatness explicit, added complete node
metadata and word proofs, and corrected the report's accounting.

Final validation: all three modules compiled in import order without errors or warnings.
An explicit scratch-copy `#print axioms` check of
`AlgebraicGeometry.exists_affine_reduction_preparation`,
`AlgebraicGeometry.exists_affine_preparation_restriction`, and
`AlgebraicGeometry.exists_reduced_flat_affine_preparation` printed exactly
`[propext, Classical.choice, Quot.sound]` for each. The scratch copy was removed.
A signature comparison confirmed the original theorem is byte-for-byte unchanged and
all three node Lean signatures match the delivered declarations. All delivered modules
contain zero `sorry`s and no forbidden declarations.
