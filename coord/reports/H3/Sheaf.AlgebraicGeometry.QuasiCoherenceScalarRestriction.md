## What changed

Proved `AlgebraicGeometry.Scheme.Modules.quasiCoherent_iff_restrictScalars` in the item module. The proof establishes that restriction of scalars preserves colimits, maps presentations to quasi-coherent modules, and glues the forward implication over the quasi-coherent cover. The affine converse is isolated in the new module `Sheaf.AlgebraicGeometry.AffineAlgebraModulePresentation`.

## Proved and sorry left

Closed hole: `AlgebraicGeometry.Scheme.Modules.quasiCoherent_iff_restrictScalars` (one original hole). Added hole: `AlgebraicGeometry.Scheme.Modules.nonempty_algebraModule_presentation_over`, with node `lem-weil-pbc-affine-algebra-module-presentation` (one split hole). This is a decomposition, with net zero holes closed; the target still depends on `sorryAx`. The forward implication and the affine-cover gluing are proved without adding holes.

## No longer needed

Removed imports: `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` (redundant public import, already publicly imported by `CommAlgebraSheaf`), `Sheaf.AlgebraicGeometry.Coherent` (proof-only), and `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage` (proof-only). The forward route uses colimit preservation, coproduct quasi-coherence, and cokernel quasi-coherence; the affine converse uses the affine presentation theorem and its affine tilde/open-restriction APIs.

The old proof dependencies no longer used directly by the item are `def-pc-scheme`,
`pqf-def-coherent`, `def-weil-sheaf-of-modules-category`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-module-restriction-open-immersion-colimits`, and
`lem-weil-pbc-quasi-coherent-module-cokernel-image`. The definitions remain statement
dependencies, and the tilde and open-restriction results remain dependencies of the new
affine split. No claim is made that these leave the whole target import closure.
The stronger cokernel-image node is replaced by the existing source-library cokernel
closure and coproduct closure nodes.

## Where the brief, the DAG or earlier work was wrong

The imported plan requires a substantial affine algebra-module presentation argument. This was absent as a separately usable Lean declaration, so it is split into the strictly smaller affine presentation theorem above. No target statement was changed.

## New nodes

`lem-weil-pbc-affine-algebra-module-presentation` records the affine free presentation and its source, searches, and Lean declaration.

## Earlier second reading (a previous round; superseded)

I reread the item node, the Stacks Lemma 0H88 statement, and both delivered modules. The item theorem has the exact original signature and proves both implications. The new affine theorem is a strict subclaim used only for the affine converse and carries the source proof details in its docstring. Both modules compile with the sandbox import closure.

The visible import change is recorded in `coord/changes/quasi-coherence-scalar-restriction-proof.md`.

## Earlier second reading (a previous round; superseded)

1. I compared both delivered modules with the repository versions. The target theorem signature is byte-for-byte unchanged; the affine presentation theorem is a new split statement. Verdict: pass.
2. I compiled both modules with `lcompile.py --all`; compilation is clean. The only remaining `sorry` is the named affine presentation theorem, with no sorry in definitions, axioms, unsafe declarations, or opaque declarations. Verdict: pass.
3. I checked the affine split against Stacks Lemma 0H88: it is the strictly smaller affine presentation subclaim used by the converse, and is not a restatement of the target. Mathlib/source searches found no existing theorem with this statement. Verdict: pass.
4. I checked the proof route and pruned it: the forward direction uses colimit preservation, coproduct quasi-coherence, and cokernel quasi-coherence; it does not use affine tilde, open restriction colimits, or the stronger cokernel-image theorem. The removed `public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` is proof-irrelevant, and the DAG proof dependencies now match the Lean route. The affine theorem keeps its required tilde and colimit imports. Verdict: pass.
5. The unit route is preserved: the target node remains realized for the same unit, while the affine presentation is recorded as a split node for the converse step. Verdict: pass.

I changed the DAG proof and dependency metadata, removed one unused public import from the target module, added explicit proof-only imports to the affine theorem module, and recorded this second reading. No target statement or existing declaration signature changed.

## Second reading by H3

1. Compared the item with the repository using a file diff and exact signature extraction.
   The existing target signature and its docstring are byte for byte unchanged. All new
   helpers are private theorems; no definitions were changed. The removed public import is
   already publicly exported by `CommAlgebraSheaf`, so the four direct importers retain
   the same API. Verdict: pass.
2. Both delivered modules compile locally. The item compiled in 40.3 seconds; a scratch
   copy with both public declarations' `#print axioms` compiled in 46.8 seconds and
   reported only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Earlier timeouts were not reproduced in this final check. There is exactly one named
   split `sorry`, no holed data or forbidden declaration, and no arbitrary witness of an
   unproved existence theorem is used to define data. Verdict: pass as a decomposition.
3. Independently checked the affine split against [Stacks 0H88](https://stacks.math.columbia.edu/tag/0H88).
   It is the affine free-presentation portion of the converse, strictly below the global
   equivalence. Its six-step docstring constructs the generators and kernel relations.
   Empty affine opens, the zero module, the zero algebra, and the identity algebra cause
   no obstruction: the same free presentation construction works, with empty generators
   where appropriate. Independent Loogle, LeanFinder, and grep searches found presentation
   constructors but no existing affine scalar-restriction presentation theorem; repository
   searches found only structure-sheaf presentations and callers of the item.
   Closing this split requires the substantive affine action comparison and is not a
   short application of one of those constructors. Verdict: pass.
4. Read the proof from the equivalence down through its private helpers. It uses the
   existing coproduct/cokernel closure theorems and forgetful colimit theorem; the new
   split is used only for the affine converse. Every old dependency absent from the new
   `proof_deps` is listed above. `sk-thm-p1.json` does not directly realize this helper
   node, and none of its realized statements or steps is bypassed or changed.
   Verdict: pass.
5. Checked both node files: the item proof and `proof_deps` match the four Lean proof
   components; the split has source, proof, searches, creation record, blueprint origin,
   chapter/unit, and Lean declaration metadata. Verdict: pass.

I corrected the report's net progress accounting, completed the removed-dependency list,
updated the import-change record to describe the actual API effect, and added this current
second reading. I did not change the Lean proofs, statements, definitions, or DAG route.
