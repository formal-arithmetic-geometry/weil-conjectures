## What changed

Preserved the existing signature and docstring of `exists_chart_completed_localizations_alpha`.
Its proof now composes two geometric comparisons through the actual section module
Γ(E, s⁻¹D(φ(f_i))). Added proof-only imports of CompletedAffineSectionLocalization and
PuncturedCompletionChartTensorSections. The original public import of
PuncturedCompletionChartSectionModules remains necessary for its statement.

CompletedAffineSectionLocalization proves
`exists_completed_affine_section_localization` for arbitrary commutative rings A and C:
affine section localization respects the localized C-action. It uses Mathlib's affine
principal-open localization, the ring-to-module localization instance, and the universal
property of module localization. PuncturedCompletionChartTensorSections states the
remaining affine pullback/overlap section comparison, separately from localization.

Removed the first reader's two proposed lemmas, their incomplete node records, the duplicate
short-name copy of the target, and the unchanged copy of PuncturedCompletionChartSectionModules
from the delivered set. No statement or definition of the repository was changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_chart_completed_localizations_alpha`.
Also proved the new generic lemma
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_completed_affine_section_localization`
(node `new-sbc-completed-affine-section-localization`), without any sorry dependency.

Added exactly one hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_chart_tensor_sections`
(node `new-sbc-punctured-completion-chart-tensor-sections`). Its docstring gives the full
natural-language affine-pullback/overlap argument and its source. There are no other sorries
in the delivered files. Compared with the repository this closes one hole and adds one:
this is a decomposition, with net zero holes closed, rather than a completed proof of the
original theorem without sorryAx. Compared with the first worker's sandbox, the two proposed
holes have been removed and replaced by one strictly geometric hole and a proved localization
step. No data definition uses a witness chosen from an unproved mere existence theorem.

## No longer needed

No existing import or module is pruned: the sole original public import is needed for the
unchanged signature. The following old direct proof dependencies are replaced in the target
node by the two geometric comparison nodes:
`def-sbc-punctured-completion-chart-section-modules`,
`def-sbc-punctured-completion-matching-sections`,
`def-weil-pbc-formal-glueing-data`, and `def-weil-pbc-adic-completion`.
These definitions are still used transitively by the new comparisons and by the target's
signature; this does not claim that their modules leave the targets' import closure.
The rejected `new-chart-completed-localizations-alpha-equiv` and
`new-chart-completed-localizations-alpha-smul` were never delivered and are omitted.

## Where the brief, the DAG or earlier work was wrong

The first worker's scalar lemma quantified over arbitrary A-linear equivalences, while its
docstring claimed a property of canonical equivalences. A-linearity alone does not supply
the displayed completed scalar compatibility; the proposed proof contained no argument
for that assertion. Neither proposed lemma had the required complete docstring proof,
their Lean signatures were not recorded verbatim in the nodes, the search lists were empty,
and the existing target node was not updated. The report incorrectly called this a proof
without distinguishing the newly introduced holes. The revised route isolates the actual
localization and affine pullback steps from the target's original plan.

## New nodes

`new-sbc-completed-affine-section-localization` records the proved affine principal-open
section localization with compatibility for the localized C-action. It has no completion,
overlap or tensor-product hypotheses, and is a genuine part of the argument.

`new-sbc-punctured-completion-chart-tensor-sections` records the remaining C-linear affine
pullback section comparison transported through the given overlap. It has no localization
of completed global sections. The two comparisons meet at a concrete section module.
No change record is needed because all existing signatures and definitions are preserved.

## Second reading by E1

1. Compared every delivered existing module with its repository version. The target signature
   is byte-for-byte unchanged, including its hypotheses, conclusion and visibility. Restored
   the original target docstring. The other two delivered modules are new; the unchanged
   dependency and duplicate short-name module were removed from the delivery.
2. Compiled the files locally in import order using lcompile.py. The target has a complete
   proof term; the generic localization lemma has a complete proof term. The only sorry is
   the named tensor-section theorem. There are no axioms, unsafe/opaque declarations,
   implemented_by/extern attributes, hollow definitions or postponed data constructions.
   Axiom checks and delivery preflight are recorded below after running them.
3. Rejected the unjustified universal scalar lemma. Checked the replacement statements on
   f=0, empty charts, the zero ring, and the empty index family. Localization and empty-chart
   sections are zero in the degenerate cases; the family assembly also works for t=0.
   The tensor-section lemma states only the affine pullback/overlap comparison, strictly
   less than the original combined localization comparison. Searched Mathlib using
   leanfinder, loogle and grep; leansearch returned Internal Server Error, recorded by
   msearch.py. Searched lean/Sheaf and lean/WeilConjectures using section, tensor and
   pullback terminology. The field-only tensor comparison in Morphisms/FiberDegree and
   flat base change of global sections do not directly apply to the arbitrary local base.
   Used the existing Mathlib localization APIs to prove the other new lemma.
4. The target now follows its original two geometric steps. Proof-only imports are private
   to the module. All old direct proof dependencies are accounted for above. Checked
   dag/units/sk-prop-input-spreading.json: this node realizes no unit statement or step;
   the unit route and its realized record are untouched.
5. Updated the existing node's proof, proof_deps and proof_origin to the composition actually
   written. New nodes include the exact Lean signatures, full proof steps, source locations,
   three kinds of recorded searches, provenance, chapter/unit and blueprint references.
   No existing DAG statement was changed.

Second reading changes: removed the first split, proved the generic affine localization
comparison (including scalar compatibility), replaced the remaining task by the affine
pullback tensor-section comparison, composed their actual equivalences, restored the target
docstring, removed extraneous delivery files, and repaired the nodes and progress accounting.

Validation: all three delivered modules compiled without warnings in import order.
Scratch-copy `#print axioms` checks show only propext, Classical.choice and Quot.sound
for exists_completed_affine_section_localization; the target and the open tensor-section
lemma additionally use sorryAx, exactly as reported. The scratch copies were removed.

Delivery validation: deliver3.py --no-push printed OK: all modules compile and preflight
passes. The delivery is classified CODEX because it adds the two comparison nodes/modules
and leaves the explicitly recorded tensor-section hole.
