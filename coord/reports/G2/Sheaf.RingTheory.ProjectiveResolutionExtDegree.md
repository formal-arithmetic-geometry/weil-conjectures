## What changed

Shortened ModuleCat.projective_resolution_ext_degree in
Sheaf.RingTheory.ProjectiveResolutionExtDegree by replacing its repeated concrete
augmentation construction with the existing proved theorem
ModuleCat.hasProjectiveResolutionLE_of_shortExact_projective_middle from
Sheaf.RingTheory.ProjectiveResolutionSuccSplice. The induction still constructs an
actual bounded resolution. Mathlib supplies the dimension constructor, projectivity
criterion, and kernel dimension shifting. Visibility is unchanged; the statement is specialized from arbitrary abelian categories with enough projectives to commutative-ring modules, using HasProjectiveResolutionLE.

Replaced the proof-only Mathlib.Algebra.Homology.Augment import with a proof-only
Sheaf.RingTheory.ProjectiveResolutionSuccSplice import. Updated the item's DAG proof,
proof_deps, and proof_origin to record this reuse. Added public imports GlobalDimension and ModuleCat.Abelian; removed the direct public import Preadditive.Projective.Resolution, which remains publicly available through GlobalDimension.
The import-direction check permits the new dependency, and the shortened module
compiles cleanly with lcompile.py.

## Proved and sorry left

ModuleCat.projective_resolution_ext_degree remains completely proved
(node lem-weil-pbc-projective-resolution-ext-degree). The starting module already
had zero sorries: zero holes closed, zero added, zero split off, zero left.
This is a duplicate-construction repair, not new hole-closing progress.
The reused splicing theorem is already proved; no dependency on an unproved
construction or newly stated theorem is introduced.

## No longer needed

Removed the direct proof import Mathlib.Algebra.Homology.Augment. The original
module's local construction of the augmented complex, its exactness proofs, its
quasi-isomorphism proof, and its ProjectiveResolution assembly are no longer
needed here: the existing splicing theorem supplies them.

No DAG nodes or Sheaf modules are pruned. Augment remains a transitive dependency
of the splicing lemma. Projective.Ext remains necessary for extMk_surjective and
extMk_zero. GlobalDimension, ModuleCat.Abelian, and Projective.Dimension are public imports. The redundant direct Ext.Basic import is removed. No realized unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The dispatch brief describes an item containing sorry, but this checkout contains
a proved resolution/dimension bridge. coord/repairs.txt still lists the upstream
#1428 duplicate-projective-dimension repair. The earlier X2 delivery already
replaced the duplicate single-degree Ext criterion with the necessary bridge
between explicit bounded resolutions and Mathlib's Ext-based dimension predicate.
The current statement is not Mathlib hasProjectiveDimensionLT_iff: the reverse
direction produces a bounded ProjectiveResolution, rather than merely repackaging
Ext vanishing. The remaining concrete splicing argument duplicated an existing
proved library lemma; this delivery removes that duplication.

The interface changes, but the existing sources of AffinePolynomialResolutionOfStalkwise, ProjectiveResolutionExtAllDegrees, and ProjectiveResolutionExtCharacterization compile unchanged against the delivered module; no forced adaptations are needed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module and node with the repository versions. The theorem interface is intentionally changed under the upstream duplicate-projective-dimension repair; the change record now records the exact old declaration, all three Lean users, and the additional DAG citer.
2. Compiled the delivered module with `lcompile.py`; it succeeds without errors or warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition, and uses only the allowed imported results.
3. Checked the specialized statement against `HasProjectiveResolutionLE` and Mathlib's `HasProjectiveDimensionLE`; it is the exact bridge required by the module callers. No new split-off statements were added.
4. Checked the proof route and pruning: the explicit augmentation duplicate is removed, while the unit's successor-resolution step is realized through the existing proved `hasProjectiveResolutionLE_of_shortExact_projective_middle` theorem. The proof-only Augment import is removed; public imports needed by the interface remain.
5. Checked the node's statement, proof, proof dependencies, and proof origin against the Lean proof. The statement-change record uses the repository declaration verbatim and lists every DAG citer.

Changed during second reading: repaired the node's malformed statement-change history, added the required change record for the interface/import change, and added this review section. No Lean proof change was needed.

The interface change is recorded in `coord/changes/projective_resolution_ext_degree.md`.

## Second reading by G2

1. Compared the delivered module with the repository version. The declaration interface differs only in the documented upstream repair from the generic abelian-category predicate to the module-specific `HasProjectiveResolutionLE` bridge; the change record names the three citers and their unchanged statements. No target statement was changed.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The proof uses only the permitted foundational axioms through its dependencies.
3. Checked the theorem statement on the zero and successor cases: the zero case is exactly projectivity via `ProjectiveResolution.self`, and the successor case uses the kernel short exact sequence and the existing splicing theorem. The statement is true and exactly the module-level bridge required by its callers; no new split-off statements were added.
4. Checked pruning and route. The duplicate augmentation construction is replaced by the proved successor-splicing theorem, while the unit's successor-resolution step remains realized. The proof-only `Mathlib.Algebra.Homology.Augment` import and redundant direct `Ext.Basic` import are removed; no required node or module is pruned.
5. Checked the DAG node against the Lean declaration. Its statement, proof steps, dependencies, source, and proof origin match the delivered proof, and the documented statement-change record records the affected citers and interface change.

Changed during this second reading: added this complete review section; no Lean proof or node repair was needed.
