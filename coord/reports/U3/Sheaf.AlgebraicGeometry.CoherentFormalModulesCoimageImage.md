## What changed

The second reader rejected the preliminary Abelian-witness split and replaced it
with the original node's affine-then-locality argument. The target module imports
`CoherentFormalModulesCoimageImageAffine` and the existing
`CoherentFormalModuleIsomorphismLocal` as proof-only imports. Its original public
imports and theorem signature remain byte for byte unchanged. The new module
states the comparison result on one affine open at one level, with the full affine
calculation documented. It does not assume or construct a global Abelian structure.

Removed the preliminary Aux module, its two new nodes, the file-level linter
suppression, and its change record. No existing definition or signature changes.

## Proved and sorry left

Closed in the item's module:
`AlgebraicGeometry.coherentFormalModules_coimageImage_isIso`.

Added one named hole:
`AlgebraicGeometry.coherentFormalModules_coimageImage_isIso_restrict_affine`
(node `lem-weil-pbc-coherent-formal-coimage-image-affine`). Its proof is exactly
`by sorry` and its docstring gives the complete affine argument, including
restriction compatibility and arbitrary kernel/cokernel choices.

This is a decomposition: one upper hole closed, one strictly local hole added,
net zero holes closed. The upper declaration still depends on sorryAx through
this lemma and the existing locality theorem; no unconditional proof is claimed.
The preliminary holes `coherentFormalModules_abelian_exists_with_instances` and
`coherentFormalModules_coimageImage_isIso_of_abelian` are removed, not proved.

## No longer needed

No original dependency module is pruned from the target's import closure.
The original locality dependency remains a direct dependency. Each of the following
old proof_deps is moved to the affine lemma's proof plan, rather than discarded:

- `lem-weil-pbc-adic-completion-noetherian`
- `lem-weil-pbc-coherent-formal-cokernel-closure`
- `lem-weil-pbc-coherent-formal-module-kernel`
- `lem-weil-pbc-coherent-formal-modules-affine`
- `lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`
- `lem-weil-pbc-module-restriction-open-immersion-colimits`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `lem-weil-pbc-quasi-coherent-module-kernel`

The corresponding seven proof imports move from the target to the new affine
module: CoherentFormalModuleKernel, CoherentFormalModulesAffine,
CoherentFormalModulesCokernelClosure, Modules.IdealTimesQuasiCoherentAffineSections,
Modules.QuasiCoherentCokernelImage, RingTheory.AdicCompletionNoetherian, and
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel. Restriction colimits
are supplied by Mathlib's restrictFunctor and restrictAdjunction, already available.
The two provisional abelian nodes and their Aux module are not delivered.

## Where the brief, the DAG or earlier work was wrong

The preliminary split assumed existence of an Abelian structure while its stated
proof required the whole coimage-image argument. This hid the assigned argument
behind a stronger statement and reversed the library's construction: the existing
CoherentFormalModulesAbelian module constructs Abelian from this very target.
The abelian comparison step was generic Mathlib machinery, not a new geometric
obligation. Adding two holes to close one was also described as a proof instead
of a decomposition. The repaired split isolates the original fixed-affine
calculation and leaves global gluing to the existing locality declaration.

## New nodes

`lem-weil-pbc-coherent-formal-coimage-image-affine` states only the restriction
of a single positive-level comparison to a fixed affine open. Its proof plan
retains the original geometric dependencies and includes the module first
isomorphism theorem and transport between universal kernel/cokernel choices.
The node and Lean docstring use Stacks 087W and 087X. No change records are needed.

## Second reading by U3

1. Compared the target with the repository using diff: its theorem signature,
   docstring, visibility and original public imports are unchanged. There are
   no changed definitions or target statements. Verdict: pass after repair.
2. Compiled both delivered modules with lcompile.py in import order, without
   errors or warnings. There is only one direct sorry, in the named affine
   theorem. No axiom, unsafe, opaque, implemented_by, extern, hollow definition,
   or data chosen from a mere unproved existence is introduced. The axiom probes
   show only propext, Classical.choice, Quot.sound and the expected sorryAx.
   Verdict: pass as a decomposition, not as an axiom-free proof of the item.
3. Rejected the two preliminary split statements. Read Stacks 087W and 087X at
   https://stacks.math.columbia.edu/tag/087W and
   https://stacks.math.columbia.edu/tag/087X because literature PDFs/source are
   absent on this machine. Checked zero arrows, zero systems, the empty affine
   open, and ideals zero and one: the universal constructions and reduction of
   module inverses remain valid. The fixed-affine fixed-level result is strictly
   one part of the original proof; it excludes global gluing. Independent rg,
   leanfinder and loogle searches found generic comparison/preservation results,
   not this specialized affine calculation (loogle reported an unknown identifier;
   LeanSearch was unavailable with Internal Server Error, recorded without a
   mathematical verdict).
   Verdict: pass; the affine geometric calculation remains open.
4. The proof uses the existing locality statement on the cover of all affine
   opens; Mathlib supplies iSup_affineOpens_eq_top. The generic abelian shortcut
   is removed. Proof-dependency imports are retained in the module holding the
   remaining obligation, and all moved dependencies are listed above. The unit
   dag/units/sk-thm-p1.json realized statement and steps are untouched; this node
   is below the unit level. Verdict: original unit route preserved, no closure
   pruning and no claimed positive net progress.
5. Read both node records against the Lean. The parent proof_deps are exactly
   the new affine lemma and the existing locality theorem. The affine node
   records the remaining original affine proof plan, complete Lean signature,
   source, searches, creation, blueprint, chapter and unit. Verdict: pass.

Changed: replaced the stronger abelian split with the affine-local decomposition,
restored the original public import, removed linter suppression and its record,
and corrected the progress accounting and node metadata.
